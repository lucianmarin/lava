/*
 * Magma — Pythonic Java Bidirectional Transpiler (single-file Java implementation).
 *
 * Magma is to Java what Pura is to C/C++ and LMON is to JSON:
 *   - Strict, lossless 1-to-1 structural equivalence with Java
 *   - Pythonic indentation (`:` blocks instead of `{` `}`, no trailing `;` noise)
 *   - Pythonic declarations (`def fn(a: i32) -> i32:`, `x: i32 = 10`, `buf: char[64]`)
 *   - Pythonic keywords & operators (`elif`, `and`, `or`, `not`, `nil`, `self`, `pass`)
 *   - Pythonic generics & collections (`list[T]`, `set[T]`, `unordered_set[T]`, `dict[K, V]`, `unordered_map[K, V]`, `Optional[T]`)
 *   - Pythonic list, set, and dict comprehensions for both Java arrays (`T[N]`) and Java collections (`ArrayList`, `TreeSet`, `HashSet`, `TreeMap`, `HashMap`)
 *   - Concise fixed-width & Java type aliases (`i8`, `i16`, `i32`, `i64`, `f32`, `f64`, `bool`, `str`, `any`) with automatic primitive/boxed resolution in generics
 *   - Auto-detected indentation (any consistent spaces or tabs) & universal newlines (\n, \r\n, \r)
 *
 * Build & CLI usage:
 *   make
 *   ./magma examples/hello.mg
 *   ./magma --magma [--indent <N|tab>] examples/hello.mg
 *   ./magma --from-java Hello.java
 *   ./magma --compile examples/hello.mg -o hello
 *   ./magma --run examples/hello.mg
 *   ./magma --check examples/hello.mg
 *   ./magma --test
 *   ./magma --bench [file.mg]
 */

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.jar.Attributes;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;
import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;

public class Magma {

    /* -------------------------------------------------------------------------
     * Public Error & Exception Types
     * ------------------------------------------------------------------------- */

    public static class MagmaException extends Exception {
        public final int line;
        public final int col;

        public MagmaException(String message, int line, int col) {
            super(message);
            this.line = line;
            this.col = col;
        }
    }

    /* -------------------------------------------------------------------------
     * Character, Token, & Type Mapping Helpers
     * ------------------------------------------------------------------------- */

    private static boolean isIdentStart(char c) {
        return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || c == '$';
    }

    private static boolean isIdentCont(char c) {
        return isIdentStart(c) || (c >= '0' && c <= '9');
    }

    private static boolean isAllCapsIdent(String s) {
        if (s.isEmpty()) return false;
        char first = s.charAt(0);
        if (!(first >= 'A' && first <= 'Z')) return false;
        boolean hasUpper = false;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c >= 'A' && c <= 'Z') hasUpper = true;
            else if (!(c == '_' || (c >= '0' && c <= '9'))) return false;
        }
        return hasUpper;
    }

    private static final String[][] SCALAR_TYPE_MAP = {
        {"i8",   "byte"},
        {"i16",  "short"},
        {"i32",  "int"},
        {"i64",  "long"},
        {"f32",  "float"},
        {"f64",  "double"},
        {"bool", "boolean"},
        {"byte", "byte"},
        {"str",  "String"},
        {"any",  "Object"}
    };

    private static final String[][] BOXED_TYPE_MAP = {
        {"i8",   "Byte"},
        {"i16",  "Short"},
        {"i32",  "Integer"},
        {"i64",  "Long"},
        {"f32",  "Float"},
        {"f64",  "Double"},
        {"bool", "Boolean"},
        {"byte", "Byte"},
        {"char", "Character"},
        {"str",  "String"},
        {"any",  "Object"}
    };

    private static final Set<String> JAVA_UTIL_CLASSES = new HashSet<>(List.of(
        "ArrayList", "LinkedList", "List", "Set", "TreeSet", "HashSet", "LinkedHashSet",
        "Map", "TreeMap", "HashMap", "LinkedHashMap", "Queue", "Deque", "ArrayDeque",
        "PriorityQueue", "Optional", "Arrays", "Collections", "Comparator", "Iterator",
        "Scanner", "UUID", "Objects", "Random", "BitSet"
    ));

    private static final Set<String> METHOD_MODIFIERS = new HashSet<>(List.of(
        "public", "private", "protected", "static", "final", "abstract",
        "synchronized", "default", "native", "strictfp"
    ));

    private static final Set<String> VAR_MODIFIERS = new HashSet<>(List.of(
        "public", "private", "protected", "static", "const", "final",
        "volatile", "transient"
    ));

    /* Scoped user-defined class/enum/interface/record tags for cast disambiguation */
    private static final Set<String> KNOWN_TAGS = new HashSet<>();

    private static void resetSymtab() {
        KNOWN_TAGS.clear();
    }

    private static void addTag(String rawHeader) {
        String s = rawHeader.trim();
        int paren = s.indexOf('(');
        if (paren >= 0) s = s.substring(0, paren).trim();
        int bracket = s.indexOf('[');
        if (bracket >= 0) s = s.substring(0, bracket).trim();
        int lt = s.indexOf('<');
        if (lt >= 0) s = s.substring(0, lt).trim();
        String[] parts = s.split("\\s+");
        if (parts.length > 0 && isIdentStart(parts[parts.length - 1].charAt(0))) {
            KNOWN_TAGS.add(parts[parts.length - 1]);
        }
    }

    private static String mapMagmaWordToJava(String w, boolean inGeneric) {
        if (inGeneric) {
            for (String[] pair : BOXED_TYPE_MAP) {
                if (pair[0].equals(w)) return pair[1];
            }
        }
        for (String[] pair : SCALAR_TYPE_MAP) {
            if (pair[0].equals(w)) return pair[1];
        }
        return switch (w) {
            case "and"   -> "&&";
            case "or"    -> "||";
            case "not"   -> "!";
            case "nil", "None" -> "null";
            case "True"  -> "true";
            case "False" -> "false";
            case "self"  -> "this";
            default      -> null;
        };
    }

    private static String mapJavaWordToMagma(String w) {
        return switch (w) {
            case "byte", "Byte"       -> "i8";
            case "short", "Short"     -> "i16";
            case "int", "Integer"     -> "i32";
            case "long", "Long"       -> "i64";
            case "float", "Float"     -> "f32";
            case "double", "Double"   -> "f64";
            case "boolean", "Boolean" -> "bool";
            case "Character"          -> "char";
            case "String"             -> "str";
            case "Object"             -> "any";
            case "null"               -> "nil";
            case "this"               -> "self";
            default                   -> null;
        };
    }

    private static boolean isMagmaScalarCastWord(String w) {
        return switch (w) {
            case "i8", "i16", "i32", "i64", "f32", "f64", "byte", "short", "int", "long", "float", "double", "char" -> true;
            default -> false;
        };
    }

    private static boolean isJavaPrimitiveCastType(String s) {
        return switch (s.trim()) {
            case "byte", "short", "int", "long", "float", "double", "char" -> true;
            default -> false;
        };
    }

    private static boolean isJavaCastTypeSlice(String raw) {
        String s = raw.trim();
        if (s.isEmpty()) return false;
        while (s.endsWith("[]")) {
            s = s.substring(0, s.length() - 2).trim();
        }
        int lt = s.indexOf('<');
        if (lt > 0 && s.endsWith(">")) {
            s = s.substring(0, lt).trim();
        }
        if (s.isEmpty() || !isIdentStart(s.charAt(0))) return false;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (!isIdentCont(c) && c != '.') return false;
        }
        if (isJavaPrimitiveCastType(s)) return true;
        if (mapJavaWordToMagma(s) != null) return true;
        if (KNOWN_TAGS.contains(s)) return true;
        if (JAVA_UTIL_CLASSES.contains(s)) return true;
        return false;
    }

    /* Find matching closing `)` for `(` at `openIdx` */
    private static int findMatchingParen(String s, int openIdx) {
        return findMatchingDelim(s, openIdx, '(', ')');
    }

    /* Find matching closing delimiter `closeCh` for `openCh` at `openIdx` */
    private static int findMatchingDelim(String s, int openIdx, char openCh, char closeCh) {
        int depth = 0;
        char quote = 0;
        int len = s.length();
        for (int i = openIdx; i < len; i++) {
            char c = s.charAt(i);
            if (quote != 0) {
                if (c == '\\' && i + 1 < len) i++;
                else if (c == quote) quote = 0;
                continue;
            }
            if (c == '"' || c == '\'') quote = c;
            else if (c == openCh) depth++;
            else if (c == closeCh) {
                depth--;
                if (depth == 0) return i;
            }
        }
        return len;
    }

    /* Split top-level comma-separated segments (respecting (), [], <>, {}) */
    private static List<String> splitTopLevelCommas(String s) {
        List<String> res = new ArrayList<>();
        int depth = 0;
        char quote = 0;
        int start = 0;
        int len = s.length();
        for (int i = 0; i < len; i++) {
            char c = s.charAt(i);
            if (quote != 0) {
                if (c == '\\' && i + 1 < len) i++;
                else if (c == quote) quote = 0;
                continue;
            }
            if (c == '"' || c == '\'') quote = c;
            else if (c == '(' || c == '[' || c == '<' || c == '{') depth++;
            else if (c == ')' || c == ']' || c == '>' || c == '}') depth--;
            else if (c == ',' && depth == 0) {
                res.add(s.substring(start, i).trim());
                start = i + 1;
            }
        }
        res.add(s.substring(start).trim());
        return res;
    }

    /* Translate a Magma type specification to Java (`list[i32]` -> `ArrayList<Integer>`, `i32[]` -> `int[]`, etc.) */
    private static String translateTypeMagmaToJava(String raw, boolean inGeneric) {
        String s = raw.trim();
        if (s.isEmpty()) return "";

        /* Handle trailing varargs `...` */
        if (s.endsWith("...")) {
            return translateTypeMagmaToJava(s.substring(0, s.length() - 3), false) + "...";
        }

        /* Handle trailing empty array brackets `[]` */
        StringBuilder arraySuffix = new StringBuilder();
        while (s.endsWith("[]")) {
            arraySuffix.append("[]");
            s = s.substring(0, s.length() - 2).trim();
        }
        boolean elemInGeneric = inGeneric && arraySuffix.length() == 0;

        /* Generic type `Base[T1, T2]` where `[` matches closing `]` at end */
        int openB = s.indexOf('[');
        if (openB > 0 && findMatchingDelim(s, openB, '[', ']') == s.length() - 1) {
            String base = s.substring(0, openB).trim();
            String inner = s.substring(openB + 1, s.length() - 1).trim();
            if (!inner.isEmpty()) {
                String javaBase = switch (base) {
                    case "list"          -> "ArrayList";
                    case "set"           -> "TreeSet";
                    case "unordered_set" -> "HashSet";
                    case "dict"          -> "TreeMap";
                    case "unordered_map" -> "HashMap";
                    default              -> translateTypeMagmaToJava(base, false);
                };
                List<String> targs = splitTopLevelCommas(inner);
                StringBuilder sb = new StringBuilder(javaBase).append('<');
                for (int i = 0; i < targs.size(); i++) {
                    if (i > 0) sb.append(", ");
                    sb.append(translateTypeMagmaToJava(targs.get(i), true));
                }
                sb.append('>').append(arraySuffix);
                return sb.toString();
            }
        }

        /* Check direct primitive/boxed word */
        String mapped = mapMagmaWordToJava(s, elemInGeneric);
        if (mapped != null) {
            return mapped + arraySuffix;
        }

        return translateTokensMagmaToJava(s) + arraySuffix;
    }

    /* Translate a Java type specification to Magma (`ArrayList<Integer>` -> `list[i32]`, `int[]` -> `i32[]`) */
    private static String translateTypeJavaToMagma(String raw) {
        String s = raw.trim();
        if (s.isEmpty()) return "";

        if (s.endsWith("...")) {
            return translateTypeJavaToMagma(s.substring(0, s.length() - 3)) + "...";
        }

        StringBuilder arraySuffix = new StringBuilder();
        while (s.endsWith("[]")) {
            arraySuffix.append("[]");
            s = s.substring(0, s.length() - 2).trim();
        }

        int openAngle = s.indexOf('<');
        if (openAngle > 0 && findMatchingDelim(s, openAngle, '<', '>') == s.length() - 1) {
            String base = s.substring(0, openAngle).trim();
            String inner = s.substring(openAngle + 1, s.length() - 1).trim();
            String magmaBase = switch (base) {
                case "ArrayList", "java.util.ArrayList" -> "list";
                case "TreeSet", "java.util.TreeSet"     -> "set";
                case "HashSet", "java.util.HashSet"     -> "unordered_set";
                case "TreeMap", "java.util.TreeMap"     -> "dict";
                case "HashMap", "java.util.HashMap"     -> "unordered_map";
                default -> translateTypeJavaToMagma(base);
            };
            if (inner.isEmpty()) {
                return magmaBase + arraySuffix;
            }
            List<String> targs = splitTopLevelCommas(inner);
            StringBuilder sb = new StringBuilder(magmaBase).append('[');
            for (int i = 0; i < targs.size(); i++) {
                if (i > 0) sb.append(", ");
                sb.append(translateTypeJavaToMagma(targs.get(i)));
            }
            sb.append(']').append(arraySuffix);
            return sb.toString();
        }

        String mapped = mapJavaWordToMagma(s);
        if (mapped != null) {
            return mapped + arraySuffix;
        }

        return translateTokensJavaToMagma(s) + arraySuffix;
    }

    private static void emitCastMagmaToJava(StringBuilder out, String typeStr, String innerStr) {
        out.append('(').append(translateTypeMagmaToJava(typeStr, false)).append(')');
        String inner = innerStr.trim();
        boolean simplePostfix = true;
        int pdepth = 0;
        for (int k = 0; k < inner.length(); k++) {
            char ic = inner.charAt(k);
            if (ic == '[' || ic == '(') pdepth++;
            else if (ic == ']' || ic == ')') pdepth--;
            else if (pdepth == 0 && (ic == ' ' || ic == '+' || ic == '-' || ic == '*' || ic == '/' ||
                                     ic == '%' || ic == '&' || ic == '|' || ic == '^' || ic == '<' || ic == '>')) {
                if ((ic == '+' || ic == '-') && k + 2 == inner.length() && inner.charAt(k + 1) == ic) continue;
                simplePostfix = false;
                break;
            }
        }
        if (simplePostfix) {
            out.append(translateTokensMagmaToJava(inner));
        } else {
            out.append('(').append(translateTokensMagmaToJava(inner)).append(')');
        }
    }

    /* Translate expression tokens from Magma to Java, respecting string/char literals */
    private static String translateTokensMagmaToJava(String s) {
        StringBuilder out = new StringBuilder(s.length() + 16);
        int len = s.length();
        int i = 0;
        while (i < len) {
            char c = s.charAt(i);
            if (c == '"' || c == '\'') {
                char quote = c;
                out.append(c);
                i++;
                while (i < len) {
                    char sc = s.charAt(i++);
                    out.append(sc);
                    if (sc == '\\' && i < len) {
                        out.append(s.charAt(i++));
                    } else if (sc == quote) {
                        break;
                    }
                }
                continue;
            }
            if (isIdentStart(c)) {
                int start = i;
                while (i < len && isIdentCont(s.charAt(i))) i++;
                String word = s.substring(start, i);
                boolean isMember = (start > 0 && s.charAt(start - 1) == '.');

                /* `new list[T](...)` / `new set[T](...)` / `new dict[K, V](...)` constructor calls */
                if (!isMember && word.equals("new") && i < len && s.charAt(i) == ' ') {
                    int ts = i;
                    while (ts < len && s.charAt(ts) == ' ') ts++;
                    int te = ts;
                    while (te < len && (isIdentCont(s.charAt(te)) || s.charAt(te) == '.')) te++;
                    if (te < len && s.charAt(te) == '[') {
                        int closeB = findMatchingDelim(s, te, '[', ']');
                        if (closeB < len && closeB + 1 < len && s.charAt(closeB + 1) == '(') {
                            String magType = s.substring(ts, closeB + 1);
                            out.append("new ").append(translateTypeMagmaToJava(magType, false));
                            i = closeB + 1;
                            continue;
                        }
                    }
                }

                /* Pythonic `cast(Type, expr)` */
                if (!isMember && word.equals("cast") && i < len && s.charAt(i) == '(') {
                    int closeP = findMatchingParen(s, i);
                    if (closeP < len) {
                        String args = s.substring(i + 1, closeP);
                        List<String> parts = splitTopLevelCommas(args);
                        if (parts.size() == 2) {
                            emitCastMagmaToJava(out, parts.get(0), parts.get(1));
                            i = closeP + 1;
                            continue;
                        }
                    }
                }

                /* Pythonic `isinstance(expr, Type)` -> `expr instanceof Type` */
                if (!isMember && word.equals("isinstance") && i < len && s.charAt(i) == '(') {
                    int closeP = findMatchingParen(s, i);
                    if (closeP < len) {
                        List<String> parts = splitTopLevelCommas(s.substring(i + 1, closeP));
                        if (parts.size() == 2) {
                            out.append(translateTokensMagmaToJava(parts.get(0)))
                               .append(" instanceof ")
                               .append(translateTypeMagmaToJava(parts.get(1), false));
                            i = closeP + 1;
                            continue;
                        }
                    }
                }

                /* Pythonic scalar value conversion: `i32(x)`, `f64(x)`, `i64(x)`, `i8(x)` -> `(int)x`, `(double)x` */
                if (!isMember && i < len && s.charAt(i) == '(' && isMagmaScalarCastWord(word)) {
                    int closeP = findMatchingParen(s, i);
                    if (closeP < len) {
                        emitCastMagmaToJava(out, word, s.substring(i + 1, closeP));
                        i = closeP + 1;
                        continue;
                    }
                }

                /* Pythonic built-in console output: `printf(...)`, `println(...)`, `print(...)` */
                if (!isMember && i < len && s.charAt(i) == '(' &&
                    (word.equals("printf") || word.equals("println") || word.equals("print"))) {
                    out.append("System.out.").append(word);
                    continue;
                }

                String rep = isMember ? null : mapMagmaWordToJava(word, false);
                if (rep != null) {
                    if (rep.equals("!") && i < len && s.charAt(i) == ' ') {
                        out.append('!');
                        i++; /* `not x` -> `!x` */
                    } else {
                        out.append(rep);
                    }
                } else {
                    out.append(word);
                }
                continue;
            }
            out.append(c);
            i++;
        }
        return out.toString();
    }

    private static boolean isJavaUnaryPrefixPos(String s, int idx) {
        while (idx > 0 && s.charAt(idx - 1) == ' ') idx--;
        if (idx == 0) return true;
        char prev = s.charAt(idx - 1);
        return prev == '(' || prev == '[' || prev == ',' || prev == '=' ||
               prev == ':' || prev == ';' || prev == '!' || prev == '?' ||
               prev == '+' || prev == '-' || prev == '*' || prev == '/' ||
               prev == '%' || prev == '&' || prev == '|' || prev == '^' ||
               prev == '<' || prev == '>';
    }

    private static int scanJavaUnaryOperand(String s, int start) {
        int len = s.length();
        int i = start;
        if (i < len && s.charAt(i) == '(') {
            int closeP = findMatchingParen(s, i);
            if (closeP < len) return closeP + 1;
        }
        while (i < len) {
            char c = s.charAt(i);
            if (isIdentCont(c) || c == '.') {
                i++;
            } else if (i + 1 < len && ((c == '+' && s.charAt(i + 1) == '+') || (c == '-' && s.charAt(i + 1) == '-'))) {
                i += 2;
            } else if (c == '(') {
                int closeP = findMatchingParen(s, i);
                if (closeP < len) i = closeP + 1;
                else break;
            } else if (c == '[') {
                int closeB = findMatchingDelim(s, i, '[', ']');
                if (closeB < len) i = closeB + 1;
                else break;
            } else {
                break;
            }
        }
        return i;
    }

    /* Translate expression tokens from Java to Magma, respecting string/char literals */
    private static String translateTokensJavaToMagma(String s) {
        StringBuilder out = new StringBuilder(s.length() + 16);
        int len = s.length();
        int i = 0;
        while (i < len) {
            char c = s.charAt(i);
            if (c == '"' || c == '\'') {
                char quote = c;
                out.append(c);
                i++;
                while (i < len) {
                    char sc = s.charAt(i++);
                    out.append(sc);
                    if (sc == '\\' && i < len) {
                        out.append(s.charAt(i++));
                    } else if (sc == quote) {
                        break;
                    }
                }
                continue;
            }

            /* `System.out.printf(`, `System.out.println(`, `System.out.print(` -> `printf(`, `println(`, `print(` */
            if (s.startsWith("System.out.printf(", i) && (i == 0 || !isIdentCont(s.charAt(i - 1)))) {
                out.append("printf(");
                i += "System.out.printf(".length();
                continue;
            }
            if (s.startsWith("System.out.println(", i) && (i == 0 || !isIdentCont(s.charAt(i - 1)))) {
                out.append("println(");
                i += "System.out.println(".length();
                continue;
            }
            if (s.startsWith("System.out.print(", i) && (i == 0 || !isIdentCont(s.charAt(i - 1)))) {
                out.append("print(");
                i += "System.out.print(".length();
                continue;
            }

            /* Logical operators: && -> and, || -> or, !x -> not x */
            if (c == '&' && i + 1 < len && s.charAt(i + 1) == '&') {
                if (out.length() > 0 && out.charAt(out.length() - 1) != ' ') out.append(' ');
                out.append("and");
                i += 2;
                if (i < len && s.charAt(i) != ' ') out.append(' ');
                continue;
            }
            if (c == '|' && i + 1 < len && s.charAt(i + 1) == '|') {
                if (out.length() > 0 && out.charAt(out.length() - 1) != ' ') out.append(' ');
                out.append("or");
                i += 2;
                if (i < len && s.charAt(i) != ' ') out.append(' ');
                continue;
            }
            if (c == '!' && (i + 1 >= len || s.charAt(i + 1) != '=')) {
                out.append("not ");
                i++;
                continue;
            }

            /* Java prefix cast `(Type)expr` -> `i32(expr)` / `f64(expr)` for primitives or `cast(Type, expr)` for objects */
            if (c == '(' && isJavaUnaryPrefixPos(s, i)) {
                int closeT = findMatchingParen(s, i);
                if (closeT < len && closeT > i + 1) {
                    String typeSlice = s.substring(i + 1, closeT).trim();
                    if (isJavaCastTypeSlice(typeSlice)) {
                        int opStart = closeT + 1;
                        while (opStart < len && s.charAt(opStart) == ' ') opStart++;
                        int opEnd = scanJavaUnaryOperand(s, opStart);
                        if (opEnd > opStart) {
                            String argSlice = s.substring(opStart, opEnd).trim();
                            if (argSlice.length() >= 2 && argSlice.charAt(0) == '(' &&
                                findMatchingParen(argSlice, 0) == argSlice.length() - 1) {
                                argSlice = argSlice.substring(1, argSlice.length() - 1).trim();
                            }
                            if (isJavaPrimitiveCastType(typeSlice)) {
                                out.append(translateTypeJavaToMagma(typeSlice))
                                   .append('(')
                                   .append(translateTokensJavaToMagma(argSlice))
                                   .append(')');
                            } else {
                                out.append("cast(")
                                   .append(translateTypeJavaToMagma(typeSlice))
                                   .append(", ")
                                   .append(translateTokensJavaToMagma(argSlice))
                                   .append(')');
                            }
                            i = opEnd;
                            continue;
                        }
                    }
                }
            }

            if (isIdentStart(c)) {
                int start = i;
                while (i < len && isIdentCont(s.charAt(i))) i++;
                String word = s.substring(start, i);
                boolean isMember = (start > 0 && s.charAt(start - 1) == '.');

                /* `new ArrayList<Integer>(...)` -> `new list[i32](...)` */
                if (!isMember && word.equals("new") && i < len && s.charAt(i) == ' ') {
                    int ts = i;
                    while (ts < len && s.charAt(ts) == ' ') ts++;
                    int te = ts;
                    while (te < len && (isIdentCont(s.charAt(te)) || s.charAt(te) == '.')) te++;
                    if (te < len && s.charAt(te) == '<') {
                        int closeA = findMatchingDelim(s, te, '<', '>');
                        if (closeA < len && closeA + 1 < len && s.charAt(closeA + 1) == '(') {
                            String jType = s.substring(ts, closeA + 1);
                            out.append("new ").append(translateTypeJavaToMagma(jType));
                            i = closeA + 1;
                            continue;
                        }
                    }
                }

                String rep = isMember ? null : mapJavaWordToMagma(word);
                if (rep != null) {
                    out.append(rep);
                } else {
                    out.append(word);
                }
                continue;
            }
            out.append(c);
            i++;
        }
        return out.toString();
    }

    /* Check if a Magma type has fixed-size array dimensions `T[N]` or `T[N][M]` (not generic `list[T]`, `dict[K, V]`, etc., and not empty `T[]`) */
    private static int findMagmaSizedArrayBracket(String typeStr) {
        String s = typeStr.trim();
        int len = s.length();
        int scanStart = 0;

        /* Skip generic type brackets if the base is a collection/generic type and closing `]` is followed by more brackets, or if base is known generic */
        int firstOpen = s.indexOf('[');
        if (firstOpen <= 0) return -1;
        String base = s.substring(0, firstOpen).trim();
        if (base.equals("list") || base.equals("set") || base.equals("unordered_set") ||
            base.equals("dict") || base.equals("unordered_map") || base.equals("Optional") ||
            base.equals("List") || base.equals("Set") || base.equals("Map")) {
            int closeB = findMatchingDelim(s, firstOpen, '[', ']');
            scanStart = (closeB < len) ? (closeB + 1) : len;
        }

        for (int i = scanStart; i < len; i++) {
            if (s.charAt(i) == '[') {
                int closeB = findMatchingDelim(s, i, '[', ']');
                if (closeB > i + 1) {
                    String dim = s.substring(i + 1, closeB).trim();
                    /* If dim is a type name (like `i32`, `str`, or contains `,`), it's a generic parameter, not an array size */
                    if (dim.contains(",") || mapMagmaWordToJava(dim, true) != null || KNOWN_TAGS.contains(dim)) {
                        return -1;
                    }
                    return i;
                }
            }
        }
        return -1;
    }

    /* Format `name: type` into Java `Type name` (or for sized arrays without `=`, `Type[] name = new Type[N]`) */
    private static String formatJavaTypedDecl(String nameStr, String typeStr, boolean allowSizedArrayAlloc) {
        String name = nameStr.trim();
        String type = typeStr.trim();
        int sizedIdx = findMagmaSizedArrayBracket(type);
        if (sizedIdx > 0) {
            String baseType = type.substring(0, sizedIdx).trim();
            String dimsRaw = type.substring(sizedIdx).trim();
            String javaElemType = translateTypeMagmaToJava(baseType, false);

            /* Count dimensions `[N][M]` -> `[][]` and translate inside each `[...]` */
            StringBuilder emptyBrackets = new StringBuilder();
            StringBuilder translatedDims = new StringBuilder();
            int i = 0;
            while (i < dimsRaw.length()) {
                if (dimsRaw.charAt(i) == '[') {
                    int closeB = findMatchingDelim(dimsRaw, i, '[', ']');
                    if (closeB < dimsRaw.length()) {
                        emptyBrackets.append("[]");
                        translatedDims.append('[')
                                      .append(translateTokensMagmaToJava(dimsRaw.substring(i + 1, closeB).trim()))
                                      .append(']');
                        i = closeB + 1;
                        continue;
                    }
                }
                i++;
            }

            if (allowSizedArrayAlloc) {
                return javaElemType + emptyBrackets + " " + translateTokensMagmaToJava(name)
                     + " = new " + javaElemType + translatedDims;
            } else {
                return javaElemType + emptyBrackets + " " + translateTokensMagmaToJava(name);
            }
        }

        return translateTypeMagmaToJava(type, false) + " " + translateTokensMagmaToJava(name);
    }

    /* Convert a Magma parameter list `(a: i32, b: str)` into Java `(int a, String b)` */
    private static String formatJavaParamList(String paramsRaw) {
        String params = paramsRaw.trim();
        if (params.isEmpty()) return "";

        List<String> parts = splitTopLevelCommas(params);
        StringBuilder out = new StringBuilder();
        boolean first = true;
        for (String p : parts) {
            if (p.isEmpty()) continue;
            if (!first) out.append(", ");
            first = false;

            int colon = p.indexOf(':');
            if (colon > 0) {
                String pname = p.substring(0, colon).trim();
                String ptype = p.substring(colon + 1).trim();
                if (pname.startsWith("const ")) {
                    pname = pname.substring(6).trim();
                    out.append("final ").append(formatJavaTypedDecl(pname, ptype, false));
                } else if (pname.startsWith("final ")) {
                    pname = pname.substring(6).trim();
                    out.append("final ").append(formatJavaTypedDecl(pname, ptype, false));
                } else {
                    out.append(formatJavaTypedDecl(pname, ptype, false));
                }
            } else {
                out.append(translateTokensMagmaToJava(p));
            }
        }
        return out.toString();
    }

    /* -------------------------------------------------------------------------
     * Magma -> Java Transpiler
     * ------------------------------------------------------------------------- */

    private enum BlockKind {
        NORMAL,
        CLASS_OR_INTERFACE,
        ENUM,
        SWITCH,
        CASE,
        DO_WHILE
    }

    private record BlockFrame(int level, BlockKind kind) {}

    private static int startsWithKw(String s, String kw) {
        if (!s.startsWith(kw)) return -1;
        int klen = kw.length();
        if (s.length() == klen) return klen;
        char next = s.charAt(klen);
        if (next == ' ' || next == '(' || next == ':') {
            int idx = klen;
            while (idx < s.length() && s.charAt(idx) == ' ') idx++;
            return idx;
        }
        return -1;
    }

    /* Split inline `#` comment outside string/char literals */
    private static String[] splitInlineHashComment(String s) {
        char quote = 0;
        int len = s.length();
        for (int i = 0; i < len; i++) {
            char c = s.charAt(i);
            if (quote != 0) {
                if (c == '\\' && i + 1 < len) i++;
                else if (c == quote) quote = 0;
                continue;
            }
            if (c == '"' || c == '\'') {
                quote = c;
                continue;
            }
            if (c == '#' && (i == 0 || s.charAt(i - 1) == ' ')) {
                int clen = i;
                while (clen > 0 && s.charAt(clen - 1) == ' ') clen--;
                return new String[]{s.substring(0, clen), s.substring(i + 1)};
            }
        }
        return new String[]{s, null};
    }

    /* Find top-level single `:` for variable/field declaration `[mods] x: type [= val]` */
    private record DeclSplit(String mods, String name, String type, String rhs) {}

    private static DeclSplit parseMagmaDecl(String s) {
        int depth = 0;
        char quote = 0;
        int colonIdx = -1;
        int eqIdx = -1;
        int len = s.length();

        for (int i = 0; i < len; i++) {
            char c = s.charAt(i);
            if (quote != 0) {
                if (c == '\\' && i + 1 < len) i++;
                else if (c == quote) quote = 0;
                continue;
            }
            if (c == '"' || c == '\'') {
                quote = c;
                continue;
            }
            if (c == '(' || c == '[' || c == '{') depth++;
            else if (c == ')' || c == ']' || c == '}') depth--;
            else if (depth == 0) {
                if (colonIdx < 0 && c == ':') {
                    if (i + 1 < len && s.charAt(i + 1) == ':') {
                        i++;
                        continue;
                    }
                    colonIdx = i;
                } else if (colonIdx >= 0 && eqIdx < 0 && c == '=') {
                    if (i + 1 < len && s.charAt(i + 1) == '=') {
                        i++;
                        continue;
                    }
                    eqIdx = i;
                    break;
                } else if (colonIdx < 0 && (c == '=' || c == ';' || c == '+' || c == '-' || c == '*' || c == '/')) {
                    return null;
                }
            }
        }
        if (colonIdx <= 0) return null;

        String lhs = s.substring(0, colonIdx).trim();
        if (lhs.isEmpty()) return null;
        for (int i = 0; i < lhs.length(); i++) {
            char c = lhs.charAt(i);
            if (!isIdentCont(c) && c != ' ') return null;
        }

        String[] lhsParts = lhs.split("\\s+");
        String varName = lhsParts[lhsParts.length - 1];
        if (!isIdentStart(varName.charAt(0))) return null;

        StringBuilder mods = new StringBuilder();
        for (int i = 0; i < lhsParts.length - 1; i++) {
            String m = lhsParts[i];
            if (!VAR_MODIFIERS.contains(m)) return null;
            if (mods.length() > 0) mods.append(' ');
            mods.append(m.equals("const") ? "final" : m);
        }

        String typePart = (eqIdx >= 0) ? s.substring(colonIdx + 1, eqIdx).trim() : s.substring(colonIdx + 1).trim();
        if (typePart.isEmpty()) return null;
        String rhsPart = (eqIdx >= 0) ? s.substring(eqIdx + 1).trim() : null;

        return new DeclSplit(mods.toString(), varName, typePart, rhsPart);
    }

    /* Try to emit a Pythonic constant `MAX_ITEMS = 64` at root or class body level */
    private static String tryEmitMagmaConstAssign(String s) {
        if (s.isEmpty() || !isIdentStart(s.charAt(0))) return null;
        int i = 0;
        int len = s.length();
        while (i < len && isIdentCont(s.charAt(i))) i++;
        String name = s.substring(0, i);
        if (!isAllCapsIdent(name)) return null;

        while (i < len && s.charAt(i) == ' ') i++;
        if (i >= len || s.charAt(i) != '=' || (i + 1 < len && s.charAt(i + 1) == '=')) return null;
        String rhs = s.substring(i + 1).trim();
        if (rhs.isEmpty()) return null;

        String inferredType = "int";
        if (rhs.startsWith("\"")) inferredType = "String";
        else if (rhs.startsWith("'")) inferredType = "char";
        else if (rhs.equals("true") || rhs.equals("false") || rhs.equals("True") || rhs.equals("False")) inferredType = "boolean";
        else if (rhs.endsWith("L") || rhs.endsWith("l")) inferredType = "long";
        else if (rhs.contains(".")) inferredType = "double";

        return "public static final " + inferredType + " " + name + " = " + translateTokensMagmaToJava(rhs) + ";";
    }

    /* Parse optional method modifiers followed by `def` or `fn` */
    private static String[] splitDefHeader(String s) {
        String trimmed = s.trim();
        int kwAfter = startsWithKw(trimmed, "def");
        if (kwAfter < 0) kwAfter = startsWithKw(trimmed, "fn");
        if (kwAfter >= 0) {
            return new String[]{"", trimmed.substring(kwAfter).trim()};
        }

        /* Check leading modifiers before ` def ` or ` fn ` */
        int defIdx = trimmed.indexOf(" def ");
        int kwLen = 5;
        if (defIdx < 0) {
            defIdx = trimmed.indexOf(" fn ");
            kwLen = 4;
        }
        if (defIdx <= 0) return null;

        String modPart = trimmed.substring(0, defIdx).trim();
        for (String tok : modPart.split("\\s+")) {
            if (!METHOD_MODIFIERS.contains(tok)) return null;
        }
        return new String[]{modPart, trimmed.substring(defIdx + kwLen).trim()};
    }

    private static String emitMagmaFunctionDef(String prefixQual, String rest, boolean isBlock) {
        int lparen = rest.indexOf('(');
        if (lparen <= 0) return null;
        int rparen = findMatchingParen(rest, lparen);
        if (rparen >= rest.length()) return null;

        String fname = rest.substring(0, lparen).trim();
        String paramsRaw = rest.substring(lparen + 1, rparen).trim();
        String after = rest.substring(rparen + 1).trim();

        String throwsClause = "";
        int throwsIdx = after.indexOf("throws ");
        if (throwsIdx >= 0) {
            throwsClause = " " + translateTokensMagmaToJava(after.substring(throwsIdx).trim());
            after = after.substring(0, throwsIdx).trim();
        }

        String retType = "void";
        boolean hasExplicitRet = false;
        if (after.startsWith("->")) {
            retType = after.substring(2).trim();
            hasExplicitRet = true;
        }

        String qual = (prefixQual == null) ? "" : prefixQual.trim();

        /* Special convenience for `main`: if `def main()` or `def main(args: str[])` is written,
           emit canonical Java `public static void main(String[] args)` when no conflicting return type is used */
        if (fname.equals("main") && (!hasExplicitRet || retType.equals("void"))) {
            String mainParams = paramsRaw.isEmpty() ? "String[] args" : formatJavaParamList(paramsRaw);
            String mainQual = qual.isEmpty() ? "public static" : qual;
            return mainQual + " void main(" + mainParams + ")" + throwsClause + (isBlock ? " {" : ";");
        }

        /* Constructor detection: starts with uppercase, no `-> ret`, and not `static` */
        boolean isConstructor = !hasExplicitRet && !fname.isEmpty() &&
                                Character.isUpperCase(fname.charAt(0)) &&
                                !qual.contains("static");

        StringBuilder out = new StringBuilder();
        if (!qual.isEmpty()) {
            out.append(qual).append(' ');
        }
        if (!isConstructor) {
            out.append(translateTypeMagmaToJava(retType, false)).append(' ');
        }
        out.append(translateTokensMagmaToJava(fname))
           .append('(')
           .append(formatJavaParamList(paramsRaw))
           .append(')')
           .append(throwsClause)
           .append(isBlock ? " {" : ";");
        return out.toString();
    }

    /* Convert Pythonic `for i in range(...)` or `for item in collection` into Java `for (...) {` */
    private static String tryEmitForIn(String expr) {
        int depth = 0;
        int inPos = -1;
        for (int i = 0; i + 4 <= expr.length(); i++) {
            char c = expr.charAt(i);
            if (c == '(' || c == '[' || c == '<') depth++;
            else if (c == ')' || c == ']' || c == '>') depth--;
            else if (depth == 0 && expr.startsWith(" in ", i)) {
                inPos = i;
                break;
            }
        }
        if (inPos < 0) return null;

        String varPart = expr.substring(0, inPos).trim();
        String rhs = expr.substring(inPos + 4).trim();

        int vcolon = varPart.indexOf(':');
        String vname = (vcolon >= 0) ? varPart.substring(0, vcolon).trim() : varPart;
        String vtype = (vcolon >= 0) ? varPart.substring(vcolon + 1).trim() : "i32";

        /* `range(stop)`, `range(start, stop)`, `range(start, stop, step)` */
        if (rhs.startsWith("range(") && findMatchingParen(rhs, 5) == rhs.length() - 1) {
            List<String> parts = splitTopLevelCommas(rhs.substring(6, rhs.length() - 1));
            if (parts.size() >= 1 && parts.size() <= 3 && !parts.get(0).isEmpty()) {
                String startS = (parts.size() == 1) ? "0" : parts.get(0);
                String stopS = (parts.size() == 1) ? parts.get(0) : parts.get(1);
                String stepS = (parts.size() == 3) ? parts.get(2) : null;
                boolean negStep = (stepS != null && stepS.startsWith("-"));

                StringBuilder sb = new StringBuilder("for (");
                sb.append(formatJavaTypedDecl(vname, vtype, false))
                  .append(" = ")
                  .append(translateTokensMagmaToJava(startS))
                  .append("; ")
                  .append(translateTokensMagmaToJava(vname))
                  .append(negStep ? " > " : " < ")
                  .append(translateTokensMagmaToJava(stopS))
                  .append("; ")
                  .append(translateTokensMagmaToJava(vname));
                if (stepS == null || stepS.equals("1")) {
                    sb.append("++");
                } else if (negStep && stepS.equals("-1")) {
                    sb.append("--");
                } else if (negStep) {
                    sb.append(" -= ").append(translateTokensMagmaToJava(stepS.substring(1).trim()));
                } else {
                    sb.append(" += ").append(translateTokensMagmaToJava(stepS));
                }
                sb.append(") {");
                return sb.toString();
            }
        }

        /* Enhanced Java foreach: `for item in vec:` -> `for (var item : vec) {` */
        StringBuilder sb = new StringBuilder("for (");
        if (vcolon >= 0) {
            sb.append(formatJavaTypedDecl(vname, vtype, false));
        } else {
            sb.append("var ").append(translateTokensMagmaToJava(vname));
        }
        sb.append(" : ").append(translateTokensMagmaToJava(rhs)).append(") {");
        return sb.toString();
    }

    private enum CompKind {
        LIST,
        SET,
        DICT
    }

    /* Emit Java initialization + loop for a Magma list/set/dict comprehension */
    private static boolean tryEmitMagmaComprehension(StringBuilder out,
                                                     String mods, String lhsName, String typeStr, String valStr,
                                                     String javaIndent, int level) {
        String val = valStr.trim();
        if (val.length() < 2) return false;

        boolean isBracket;
        if (val.charAt(0) == '[' && findMatchingDelim(val, 0, '[', ']') == val.length() - 1) {
            isBracket = true;
        } else if (val.charAt(0) == '{' && findMatchingDelim(val, 0, '{', '}') == val.length() - 1) {
            isBracket = false;
        } else {
            return false;
        }

        String inner = val.substring(1, val.length() - 1);
        int forIdx = -1;
        int depth = 0;
        char quote = 0;
        for (int i = 0; i + 5 <= inner.length(); i++) {
            char c = inner.charAt(i);
            if (quote != 0) {
                if (c == '\\' && i + 1 < inner.length()) i++;
                else if (c == quote) quote = 0;
                continue;
            }
            if (c == '"' || c == '\'') quote = c;
            else if (c == '(' || c == '[' || c == '{') depth++;
            else if (c == ')' || c == ']' || c == '}') depth--;
            else if (depth == 0 && inner.startsWith(" for ", i)) {
                forIdx = i;
                break;
            }
        }
        if (forIdx < 0) return false;

        String head = inner.substring(0, forIdx).trim();
        if (head.isEmpty()) return false;

        String afterFor = inner.substring(forIdx + 5);
        int inIdx = -1;
        int ifIdx = -1;
        depth = 0;
        quote = 0;
        for (int i = 0; i < afterFor.length(); i++) {
            char c = afterFor.charAt(i);
            if (quote != 0) {
                if (c == '\\' && i + 1 < afterFor.length()) i++;
                else if (c == quote) quote = 0;
                continue;
            }
            if (c == '"' || c == '\'') quote = c;
            else if (c == '(' || c == '[' || c == '{') depth++;
            else if (c == ')' || c == ']' || c == '}') depth--;
            else if (depth == 0) {
                if (inIdx < 0 && i + 4 <= afterFor.length() && afterFor.startsWith(" in ", i)) {
                    inIdx = i;
                } else if (inIdx >= 0 && i + 4 <= afterFor.length() && afterFor.startsWith(" if ", i)) {
                    ifIdx = i;
                    break;
                }
            }
        }
        if (inIdx < 0) return false;

        String forClause = (ifIdx >= 0 ? afterFor.substring(0, ifIdx) : afterFor).trim();
        String condStr = (ifIdx >= 0) ? afterFor.substring(ifIdx + 4).trim() : null;
        if (condStr != null && condStr.isEmpty()) return false;

        String vname = afterFor.substring(0, inIdx).trim();
        int vcolon = vname.indexOf(':');
        if (vcolon >= 0) vname = vname.substring(0, vcolon).trim();
        if (vname.isEmpty()) return false;

        CompKind kind = CompKind.LIST;
        String keyStr = null;
        String elemStr = head;

        if (!isBracket) {
            int colonIdx = -1;
            depth = 0;
            quote = 0;
            int qmarkDepth = 0;
            for (int i = 0; i < head.length(); i++) {
                char c = head.charAt(i);
                if (quote != 0) {
                    if (c == '\\' && i + 1 < head.length()) i++;
                    else if (c == quote) quote = 0;
                    continue;
                }
                if (c == '"' || c == '\'') quote = c;
                else if (c == '(' || c == '[' || c == '{') depth++;
                else if (c == ')' || c == ']' || c == '}') depth--;
                else if (depth == 0) {
                    if (c == '?') qmarkDepth++;
                    else if (c == ':') {
                        if (i + 1 < head.length() && head.charAt(i + 1) == ':') i++;
                        else if (qmarkDepth > 0) qmarkDepth--;
                        else { colonIdx = i; break; }
                    }
                }
            }
            if (colonIdx >= 0) {
                kind = CompKind.DICT;
                keyStr = head.substring(0, colonIdx).trim();
                elemStr = head.substring(colonIdx + 1).trim();
                if (keyStr.isEmpty() || elemStr.isEmpty()) return false;
            } else {
                kind = CompKind.SET;
            }
        }

        int sizedArrIdx = findMagmaSizedArrayBracket(typeStr);
        boolean isJavaArray = (sizedArrIdx > 0);

        /* Emit declaration line */
        if (!mods.isEmpty()) out.append(mods).append(' ');
        if (isJavaArray) {
            out.append(formatJavaTypedDecl(lhsName, typeStr, true)).append(";\n");
        } else {
            String javaType = translateTypeMagmaToJava(typeStr, false);
            int angleIdx = javaType.indexOf('<');
            String rawCollection = (angleIdx > 0) ? javaType.substring(0, angleIdx) : javaType;
            out.append(javaType).append(' ').append(translateTokensMagmaToJava(lhsName))
               .append(" = new ").append(rawCollection).append("<>();\n");
        }

        /* Emit `for (...) {` */
        appendIndent(out, javaIndent, level);
        String forHeader = tryEmitForIn(forClause);
        if (forHeader != null) {
            out.append(forHeader).append('\n');
        } else {
            out.append("for (").append(translateTokensMagmaToJava(forClause)).append(") {\n");
        }

        /* Optional `if (cond) {` filter */
        if (condStr != null) {
            appendIndent(out, javaIndent, level + 1);
            out.append("if (").append(translateTokensMagmaToJava(condStr)).append(") {\n");
        }

        int bodyLevel = level + (condStr != null ? 2 : 1);
        appendIndent(out, javaIndent, bodyLevel);
        out.append(translateTokensMagmaToJava(lhsName));

        if (kind == CompKind.LIST) {
            if (isJavaArray) {
                out.append('[').append(translateTokensMagmaToJava(vname)).append("] = ")
                   .append(translateTokensMagmaToJava(elemStr)).append(";\n");
            } else {
                out.append(".add(").append(translateTokensMagmaToJava(elemStr)).append(");\n");
            }
        } else if (kind == CompKind.SET) {
            if (isJavaArray) {
                out.append('[').append(translateTokensMagmaToJava(elemStr)).append("] = true;\n");
            } else {
                out.append(".add(").append(translateTokensMagmaToJava(elemStr)).append(");\n");
            }
        } else {
            if (isJavaArray) {
                out.append('[').append(translateTokensMagmaToJava(keyStr)).append("] = ")
                   .append(translateTokensMagmaToJava(elemStr)).append(";\n");
            } else {
                out.append(".put(").append(translateTokensMagmaToJava(keyStr)).append(", ")
                   .append(translateTokensMagmaToJava(elemStr)).append(");\n");
            }
        }

        if (condStr != null) {
            appendIndent(out, javaIndent, level + 1);
            out.append("}\n");
        }

        appendIndent(out, javaIndent, level);
        out.append('}');
        return true;
    }

    private static void appendIndent(StringBuilder out, String unit, int level) {
        for (int i = 0; i < level; i++) {
            out.append(unit);
        }
    }

    private static void closeBlockFrame(StringBuilder out, BlockFrame frame, String javaIndent) {
        if (frame.kind() == BlockKind.CASE) return;
        appendIndent(out, javaIndent, frame.level());
        out.append("}\n");
    }

    private static String transformClassHeaderMagmaToJava(String header) {
        String h = header.trim();
        if (h.startsWith("struct ")) {
            h = "static class " + h.substring(7).trim();
        }
        addTag(h);

        /* Record header `record Vec2(x: f64, y: f64)` */
        int recIdx = h.indexOf("record ");
        if (recIdx >= 0) {
            int lp = h.indexOf('(', recIdx);
            int rp = (lp >= 0) ? findMatchingParen(h, lp) : -1;
            if (lp > 0 && rp > lp) {
                String before = h.substring(0, lp).trim();
                String params = formatJavaParamList(h.substring(lp + 1, rp));
                String after = h.substring(rp + 1).trim();
                return translateTokensMagmaToJava(before) + "(" + params + ")" +
                       (after.isEmpty() ? "" : " " + translateTokensMagmaToJava(after));
            }
        }

        /* Class inheritance `class Dog(Animal)` -> `class Dog extends Animal` */
        int lp = h.indexOf('(');
        int rp = (lp >= 0) ? findMatchingParen(h, lp) : -1;
        if (lp > 0 && rp > lp) {
            String before = h.substring(0, lp).trim();
            String base = h.substring(lp + 1, rp).trim();
            String after = h.substring(rp + 1).trim();
            return translateTokensMagmaToJava(before) + " extends " + translateTypeMagmaToJava(base, false) +
                   (after.isEmpty() ? "" : " " + translateTokensMagmaToJava(after));
        }

        return translateTokensMagmaToJava(h);
    }

    public static String magmaToJava(String src) throws MagmaException {
        if (!src.isEmpty() && src.charAt(0) == '\uFEFF') {
            throw new MagmaException("UTF-8 BOM is not allowed", 1, 1);
        }

        resetSymtab();
        StringBuilder out = new StringBuilder(src.length() * 2 + 128);

        char indentChar = 0;
        int indentWidth = 0;
        List<BlockFrame> stack = new ArrayList<>();
        int currentLevel = 0;
        boolean prevLineOpenedBlock = false;
        int prevBlockLine = 0;

        String javaIndent = "    ";
        int p = 0;
        int len = src.length();
        int lineNo = 0;

        while (p < len) {
            lineNo++;
            int lineStart = p;
            while (p < len && src.charAt(p) != '\n' && src.charAt(p) != '\r') p++;
            int lineEnd = p;
            if (p < len) {
                if (src.charAt(p) == '\r' && p + 1 < len && src.charAt(p + 1) == '\n') p += 2;
                else p++;
            }

            int ws = 0;
            boolean hasSpace = false;
            boolean hasTab = false;
            while (lineStart + ws < lineEnd) {
                char c = src.charAt(lineStart + ws);
                if (c == ' ') { hasSpace = true; ws++; }
                else if (c == '\t') { hasTab = true; ws++; }
                else break;
            }

            if (lineStart + ws == lineEnd) {
                out.append('\n');
                continue;
            }

            if (hasSpace && hasTab) {
                throw new MagmaException("mixed spaces and tabs in indentation", lineNo, ws);
            }

            char lastCh = src.charAt(lineEnd - 1);
            if (lastCh == ' ' || lastCh == '\t') {
                throw new MagmaException("trailing whitespace is not allowed", lineNo, lineEnd - lineStart);
            }

            int level = 0;
            if (ws > 0) {
                char ch = hasTab ? '\t' : ' ';
                if (indentWidth == 0) {
                    if (currentLevel == 0 && !prevLineOpenedBlock) {
                        throw new MagmaException("unexpected indentation at root level", lineNo, 1);
                    }
                    indentChar = ch;
                    indentWidth = ws;
                    level = 1;
                } else {
                    if (ch != indentChar) {
                        throw new MagmaException("inconsistent indentation character (spaces vs tabs)", lineNo, 1);
                    }
                    if (ws % indentWidth != 0) {
                        throw new MagmaException("indentation is not a multiple of the file's indent unit", lineNo, ws + 1);
                    }
                    level = ws / indentWidth;
                }
            }

            String rawContent = src.substring(lineStart + ws, lineEnd);

            if (prevLineOpenedBlock && rawContent.charAt(0) != '#') {
                if (level != currentLevel) {
                    throw new MagmaException("expected indented block after ':'", prevBlockLine, 1);
                }
                prevLineOpenedBlock = false;
            } else if (!prevLineOpenedBlock && level > currentLevel && rawContent.charAt(0) != '#') {
                throw new MagmaException("unexpected indentation increase without a block header", lineNo, ws + 1);
            }

            /* Full-line `#` comment */
            if (rawContent.charAt(0) == '#') {
                appendIndent(out, javaIndent, level);
                out.append("//").append(rawContent.substring(1)).append('\n');
                continue;
            }

            String[] split = splitInlineHashComment(rawContent);
            String content = split[0];
            String inlineComment = split[1];

            int kwAfter;
            boolean isElif = startsWithKw(content, "elif") >= 0;
            boolean isElse = content.equals("else:");
            boolean isCatch = startsWithKw(content, "catch") >= 0 || startsWithKw(content, "except") >= 0;
            boolean isFinally = content.equals("finally:");
            boolean isCase = startsWithKw(content, "case") >= 0 || content.equals("default:");

            /* Close blocks down to `level` */
            while (!stack.isEmpty() && stack.get(stack.size() - 1).level() >= level) {
                BlockFrame top = stack.get(stack.size() - 1);
                if (top.level() == level && top.kind() == BlockKind.NORMAL &&
                    (isElif || isElse || isCatch || isFinally)) {
                    break;
                }
                if (top.level() == level && top.kind() == BlockKind.CASE && isCase) {
                    stack.remove(stack.size() - 1);
                    break;
                }
                if (top.level() == level && top.kind() == BlockKind.DO_WHILE &&
                    startsWithKw(content, "while") >= 0 && !content.endsWith(":")) {
                    break;
                }
                stack.remove(stack.size() - 1);
                closeBlockFrame(out, top, javaIndent);
            }
            currentLevel = level;

            /* `do:` closed by `while cond` at same level */
            if (!stack.isEmpty() && stack.get(stack.size() - 1).level() == level &&
                stack.get(stack.size() - 1).kind() == BlockKind.DO_WHILE &&
                (kwAfter = startsWithKw(content, "while")) >= 0 && !content.endsWith(":")) {
                stack.remove(stack.size() - 1);
                appendIndent(out, javaIndent, level);
                out.append("} while (").append(translateTokensMagmaToJava(content.substring(kwAfter))).append(");");
                if (inlineComment != null) out.append(" //").append(inlineComment);
                out.append('\n');
                continue;
            }

            /* `pass` no-op inside empty block */
            if (content.equals("pass")) {
                if (inlineComment != null) {
                    appendIndent(out, javaIndent, level);
                    out.append("//").append(inlineComment).append('\n');
                }
                continue;
            }

            /* `package ...` and `import ...` / `from ... import ...` */
            if ((kwAfter = startsWithKw(content, "package")) >= 0) {
                appendIndent(out, javaIndent, level);
                out.append("package ").append(content.substring(kwAfter).trim()).append(';');
                if (inlineComment != null) out.append(" //").append(inlineComment);
                out.append('\n');
                continue;
            }
            if ((kwAfter = startsWithKw(content, "import")) >= 0) {
                appendIndent(out, javaIndent, level);
                String imp = content.substring(kwAfter).trim();
                if (!imp.contains(".") && !imp.startsWith("static ") && JAVA_UTIL_CLASSES.contains(imp)) {
                    imp = "java.util." + imp;
                }
                out.append("import ").append(imp).append(';');
                if (inlineComment != null) out.append(" //").append(inlineComment);
                out.append('\n');
                continue;
            }
            if ((kwAfter = startsWithKw(content, "from")) >= 0) {
                appendIndent(out, javaIndent, level);
                String restFrom = content.substring(kwAfter).trim();
                int impPos = restFrom.indexOf(" import ");
                if (impPos > 0) {
                    String pkg = restFrom.substring(0, impPos).trim();
                    String sym = restFrom.substring(impPos + 8).trim();
                    out.append("import ").append(pkg).append('.').append(sym).append(';');
                } else {
                    out.append("import ").append(restFrom).append(';');
                }
                if (inlineComment != null) out.append(" //").append(inlineComment);
                out.append('\n');
                continue;
            }

            /* Standalone annotation `@Override` */
            if (content.startsWith("@") && !content.endsWith(":")) {
                appendIndent(out, javaIndent, level);
                out.append(translateTokensMagmaToJava(content));
                if (inlineComment != null) out.append(" //").append(inlineComment);
                out.append('\n');
                continue;
            }

            /* Block header ending with `:` */
            if (content.endsWith(":")) {
                String header = content.substring(0, content.length() - 1).trim();

                if (isElif && !stack.isEmpty() && stack.get(stack.size() - 1).level() == level) {
                    kwAfter = startsWithKw(header, "elif");
                    appendIndent(out, javaIndent, level);
                    out.append("} else if (").append(translateTokensMagmaToJava(header.substring(kwAfter))).append(") {");
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if (isElse && !stack.isEmpty() && stack.get(stack.size() - 1).level() == level) {
                    appendIndent(out, javaIndent, level);
                    out.append("} else {");
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if (isCatch && !stack.isEmpty() && stack.get(stack.size() - 1).level() == level) {
                    kwAfter = startsWithKw(header, "catch");
                    if (kwAfter < 0) kwAfter = startsWithKw(header, "except");
                    String cexpr = header.substring(kwAfter).trim();
                    if (cexpr.startsWith("(") && cexpr.endsWith(")")) {
                        cexpr = cexpr.substring(1, cexpr.length() - 1).trim();
                    }
                    appendIndent(out, javaIndent, level);
                    out.append("} catch (")
                       .append(cexpr.isEmpty() ? "Exception e" : formatJavaParamList(cexpr))
                       .append(") {");
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if (isFinally && !stack.isEmpty() && stack.get(stack.size() - 1).level() == level) {
                    appendIndent(out, javaIndent, level);
                    out.append("} finally {");
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if ((kwAfter = startsWithKw(header, "if")) >= 0) {
                    appendIndent(out, javaIndent, level);
                    out.append("if (").append(translateTokensMagmaToJava(header.substring(kwAfter))).append(") {");
                    stack.add(new BlockFrame(level, BlockKind.NORMAL));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if ((kwAfter = startsWithKw(header, "while")) >= 0) {
                    appendIndent(out, javaIndent, level);
                    out.append("while (").append(translateTokensMagmaToJava(header.substring(kwAfter))).append(") {");
                    stack.add(new BlockFrame(level, BlockKind.NORMAL));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if (header.equals("do")) {
                    appendIndent(out, javaIndent, level);
                    out.append("do {");
                    stack.add(new BlockFrame(level, BlockKind.DO_WHILE));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if ((kwAfter = startsWithKw(header, "for")) >= 0) {
                    appendIndent(out, javaIndent, level);
                    String fexpr = header.substring(kwAfter).trim();
                    String forIn = tryEmitForIn(fexpr);
                    if (forIn != null) {
                        out.append(forIn);
                    } else {
                        out.append("for (");
                        int semi1 = fexpr.indexOf(';');
                        if (semi1 > 0) {
                            String initPart = fexpr.substring(0, semi1).trim();
                            DeclSplit ds = parseMagmaDecl(initPart);
                            if (ds != null) {
                                if (!ds.mods().isEmpty()) out.append(ds.mods()).append(' ');
                                out.append(formatJavaTypedDecl(ds.name(), ds.type(), false));
                                if (ds.rhs() != null) {
                                    out.append(" = ").append(translateTokensMagmaToJava(ds.rhs()));
                                }
                            } else {
                                out.append(translateTokensMagmaToJava(initPart));
                            }
                            out.append(translateTokensMagmaToJava(fexpr.substring(semi1)));
                        } else {
                            out.append(translateTokensMagmaToJava(fexpr));
                        }
                        out.append(") {");
                    }
                    stack.add(new BlockFrame(level, BlockKind.NORMAL));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if ((kwAfter = startsWithKw(header, "switch")) >= 0 ||
                           (kwAfter = startsWithKw(header, "match")) >= 0) {
                    appendIndent(out, javaIndent, level);
                    out.append("switch (").append(translateTokensMagmaToJava(header.substring(kwAfter))).append(") {");
                    stack.add(new BlockFrame(level, BlockKind.SWITCH));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if ((kwAfter = startsWithKw(header, "case")) >= 0) {
                    appendIndent(out, javaIndent, level);
                    out.append("case ").append(translateTokensMagmaToJava(header.substring(kwAfter))).append(':');
                    stack.add(new BlockFrame(level, BlockKind.CASE));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if (header.equals("default")) {
                    appendIndent(out, javaIndent, level);
                    out.append("default:");
                    stack.add(new BlockFrame(level, BlockKind.CASE));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if (header.equals("try")) {
                    appendIndent(out, javaIndent, level);
                    out.append("try {");
                    stack.add(new BlockFrame(level, BlockKind.NORMAL));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if ((kwAfter = startsWithKw(header, "synchronized")) >= 0 && splitDefHeader(header) == null) {
                    appendIndent(out, javaIndent, level);
                    String syncExpr = header.substring(kwAfter).trim();
                    if (syncExpr.startsWith("(") && syncExpr.endsWith(")")) {
                        syncExpr = syncExpr.substring(1, syncExpr.length() - 1).trim();
                    }
                    out.append("synchronized (").append(translateTokensMagmaToJava(syncExpr)).append(") {");
                    stack.add(new BlockFrame(level, BlockKind.NORMAL));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if (header.contains("enum ") || header.startsWith("enum ")) {
                    addTag(header);
                    appendIndent(out, javaIndent, level);
                    out.append(translateTokensMagmaToJava(header)).append(" {");
                    stack.add(new BlockFrame(level, BlockKind.ENUM));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else if (header.startsWith("class ") || header.contains(" class ") ||
                           header.startsWith("interface ") || header.contains(" interface ") ||
                           header.startsWith("record ") || header.contains(" record ") ||
                           header.startsWith("struct ")) {
                    appendIndent(out, javaIndent, level);
                    out.append(transformClassHeaderMagmaToJava(header)).append(" {");
                    stack.add(new BlockFrame(level, BlockKind.CLASS_OR_INTERFACE));
                    currentLevel = level + 1;
                    prevLineOpenedBlock = true;
                    prevBlockLine = lineNo;
                } else {
                    String[] defParts = splitDefHeader(header);
                    if (defParts != null) {
                        appendIndent(out, javaIndent, level);
                        String fnJava = emitMagmaFunctionDef(defParts[0], defParts[1], true);
                        if (fnJava == null) {
                            throw new MagmaException("invalid function definition", lineNo, 1);
                        }
                        out.append(fnJava);
                        stack.add(new BlockFrame(level, BlockKind.NORMAL));
                        currentLevel = level + 1;
                        prevLineOpenedBlock = true;
                        prevBlockLine = lineNo;
                    } else {
                        appendIndent(out, javaIndent, level);
                        out.append(translateTokensMagmaToJava(header)).append(" {");
                        stack.add(new BlockFrame(level, BlockKind.NORMAL));
                        currentLevel = level + 1;
                        prevLineOpenedBlock = true;
                        prevBlockLine = lineNo;
                    }
                }

                if (inlineComment != null) out.append(" //").append(inlineComment);
                out.append('\n');
                continue;
            }

            /* Non-block statement at `level` */
            appendIndent(out, javaIndent, level);

            /* Inside an `enum` block, constants are comma-separated */
            if (!stack.isEmpty() && stack.get(stack.size() - 1).kind() == BlockKind.ENUM &&
                stack.get(stack.size() - 1).level() + 1 == level) {
                out.append(translateTokensMagmaToJava(content));
                if (!content.endsWith(",") && !content.endsWith(";")) {
                    out.append(',');
                }
                if (inlineComment != null) out.append(" //").append(inlineComment);
                out.append('\n');
                continue;
            }

            /* Single-line `record Name(x: f64, y: f64)` without `:` */
            if (content.startsWith("record ") || content.contains(" record ")) {
                out.append(transformClassHeaderMagmaToJava(content)).append(" {}");
                if (inlineComment != null) out.append(" //").append(inlineComment);
                out.append('\n');
                continue;
            }

            /* Method prototype without body (interface / abstract method) */
            String[] defProto = splitDefHeader(content);
            if (defProto != null) {
                String fnJava = emitMagmaFunctionDef(defProto[0], defProto[1], false);
                if (fnJava == null) {
                    throw new MagmaException("invalid method prototype", lineNo, 1);
                }
                out.append(fnJava);
                if (inlineComment != null) out.append(" //").append(inlineComment);
                out.append('\n');
                continue;
            }

            /* Variable or field declaration: `[mods] name: type [= value]` */
            DeclSplit ds = parseMagmaDecl(content);
            if (ds != null) {
                if (ds.rhs() != null) {
                    if (!tryEmitMagmaComprehension(out, ds.mods(), ds.name(), ds.type(), ds.rhs(), javaIndent, level)) {
                        if (!ds.mods().isEmpty()) out.append(ds.mods()).append(' ');
                        out.append(formatJavaTypedDecl(ds.name(), ds.type(), false))
                           .append(" = ")
                           .append(translateTokensMagmaToJava(ds.rhs()))
                           .append(';');
                    }
                } else {
                    if (!ds.mods().isEmpty()) out.append(ds.mods()).append(' ');
                    out.append(formatJavaTypedDecl(ds.name(), ds.type(), true)).append(';');
                }
            } else {
                boolean inClassScope = (level == 0) ||
                    (!stack.isEmpty() && stack.get(stack.size() - 1).kind() == BlockKind.CLASS_OR_INTERFACE &&
                     stack.get(stack.size() - 1).level() + 1 == level);
                String constJava = inClassScope ? tryEmitMagmaConstAssign(content) : null;
                if (constJava != null) {
                    out.append(constJava);
                } else {
                    out.append(translateTokensMagmaToJava(content));
                    if (!content.endsWith(";") && !content.endsWith(",")) {
                        out.append(';');
                    }
                }
            }

            if (inlineComment != null) out.append(" //").append(inlineComment);
            out.append('\n');
        }

        if (prevLineOpenedBlock) {
            throw new MagmaException("dangling block header at end of file (expected indented block)", prevBlockLine, 1);
        }

        while (!stack.isEmpty()) {
            BlockFrame top = stack.remove(stack.size() - 1);
            closeBlockFrame(out, top, javaIndent);
        }

        return out.toString();
    }

    /* -------------------------------------------------------------------------
     * Java -> Magma Transpiler & Canonical Magma Formatter
     * ------------------------------------------------------------------------- */

    private static boolean isValidIndentUnit(String unit) {
        if (unit == null || unit.isEmpty()) return false;
        char ch = unit.charAt(0);
        if (ch != ' ' && ch != '\t') return false;
        for (int i = 1; i < unit.length(); i++) {
            if (unit.charAt(i) != ch) return false;
        }
        return true;
    }

    /* Convert a Java parameter `final String[] args` or `int a` into Magma `const args: str[]` or `a: i32` */
    private static String emitMagmaParam(String rawParam) {
        String p = rawParam.trim();
        if (p.isEmpty()) return "";

        boolean isFinal = false;
        if (p.startsWith("final ")) {
            isFinal = true;
            p = p.substring(6).trim();
        }

        /* Handle C-style array brackets attached to param name `int arr[]` */
        String trailingBrackets = "";
        while (p.endsWith("[]")) {
            trailingBrackets = "[]" + trailingBrackets;
            p = p.substring(0, p.length() - 2).trim();
        }

        int idEnd = p.length();
        int idStart = idEnd;
        while (idStart > 0 && isIdentCont(p.charAt(idStart - 1))) idStart--;
        if (idStart == 0 || idStart == idEnd) {
            return translateTokensJavaToMagma(rawParam.trim());
        }

        String name = p.substring(idStart, idEnd);
        String typePart = p.substring(0, idStart).trim() + trailingBrackets;

        return (isFinal ? "const " : "") + name + ": " + translateTypeJavaToMagma(typePart);
    }

    /* Convert a Java method/constructor header into `[mods] def name(params) [-> ret_type]:` */
    private static String tryEmitJavaFuncToMagma(String s, boolean isBlock) {
        if (startsWithKw(s, "if") >= 0 || startsWithKw(s, "for") >= 0 ||
            startsWithKw(s, "while") >= 0 || startsWithKw(s, "switch") >= 0 ||
            startsWithKw(s, "catch") >= 0 || startsWithKw(s, "synchronized") >= 0 ||
            startsWithKw(s, "class") >= 0 || startsWithKw(s, "interface") >= 0 ||
            startsWithKw(s, "enum") >= 0 || startsWithKw(s, "record") >= 0 ||
            s.contains(" class ") || s.contains(" interface ") || s.contains(" enum ") || s.contains(" record ")) {
            return null;
        }

        int lparen = s.indexOf('(');
        if (lparen <= 0) return null;
        if (s.substring(0, lparen).contains("=")) return null;
        int rparen = findMatchingParen(s, lparen);
        if (rparen >= s.length()) return null;

        String pre = s.substring(0, lparen).trim();
        int fnStart = pre.length();
        while (fnStart > 0 && isIdentCont(pre.charAt(fnStart - 1))) fnStart--;
        if (fnStart == pre.length()) return null;
        if (fnStart > 0 && pre.charAt(fnStart - 1) != ' ') return null;

        String fnName = pre.substring(fnStart).trim();
        String beforeName = pre.substring(0, fnStart).trim();

        /* Separate leading method modifiers (`public`, `static`, etc.) from return type */
        StringBuilder mods = new StringBuilder();
        String retType = "";
        if (!beforeName.isEmpty()) {
            int i = 0;
            int blen = beforeName.length();
            while (i < blen) {
                while (i < blen && beforeName.charAt(i) == ' ') i++;
                int ws = i;
                while (i < blen && isIdentCont(beforeName.charAt(i))) i++;
                String tok = beforeName.substring(ws, i);
                if (!tok.isEmpty() && METHOD_MODIFIERS.contains(tok) &&
                    (i == blen || beforeName.charAt(i) == ' ')) {
                    if (mods.length() > 0) mods.append(' ');
                    mods.append(tok);
                } else {
                    retType = beforeName.substring(ws).trim();
                    break;
                }
            }
        }

        /* Must either have a return type OR be a constructor block (uppercase name) */
        if (retType.isEmpty() && (!isBlock || !Character.isUpperCase(fnName.charAt(0)))) {
            return null;
        }
        if (retType.equals("return") || retType.equals("new") || retType.equals("throw") ||
            retType.equals("else") || retType.equals("case")) {
            return null;
        }
        for (int i = 0; i < retType.length(); i++) {
            char c = retType.charAt(i);
            if (!isIdentCont(c) && c != ' ' && c != '<' && c != '>' && c != '[' && c != ']' && c != ',' && c != '.') {
                return null;
            }
        }

        String paramsRaw = s.substring(lparen + 1, rparen).trim();
        List<String> paramItems = paramsRaw.isEmpty() ? List.of() : splitTopLevelCommas(paramsRaw);
        for (String item : paramItems) {
            String p = item.trim();
            if (p.isEmpty()) continue;
            if (p.contains("\"") || p.contains("'") || p.contains("+") || p.contains("-") || p.contains("=")) {
                return null;
            }
        }

        StringBuilder out = new StringBuilder();
        if (mods.length() > 0) {
            out.append(mods).append(' ');
        }
        out.append("def ").append(fnName).append('(');
        boolean first = true;
        for (String item : paramItems) {
            if (item.isEmpty()) continue;
            if (!first) out.append(", ");
            first = false;
            out.append(emitMagmaParam(item));
        }
        out.append(')');

        String afterRp = s.substring(rparen + 1).trim();
        if (!retType.isEmpty() && !retType.equals("void")) {
            out.append(" -> ").append(translateTypeJavaToMagma(retType));
        }
        if (!afterRp.isEmpty()) {
            out.append(' ').append(translateTokensJavaToMagma(afterRp));
        }
        if (isBlock) out.append(':');
        return out.toString();
    }

    /* Convert a Java variable/field declaration `int x = 10` or `double[] r = new double[3]` to Magma `x: i32 = 10` or `r: f64[3]` */
    private static String tryEmitJavaVarDeclToMagma(String s, boolean inClassScope) {
        if (startsWithKw(s, "return") >= 0 || startsWithKw(s, "break") >= 0 ||
            startsWithKw(s, "continue") >= 0 || startsWithKw(s, "throw") >= 0 ||
            startsWithKw(s, "case") >= 0 || startsWithKw(s, "package") >= 0 ||
            startsWithKw(s, "import") >= 0) {
            return null;
        }

        /* Split at first top-level `=` if present */
        int eqIdx = -1;
        int depth = 0;
        char quote = 0;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (quote != 0) {
                if (c == '\\' && i + 1 < s.length()) i++;
                else if (c == quote) quote = 0;
                continue;
            }
            if (c == '"' || c == '\'') quote = c;
            else if (c == '(' || c == '[' || c == '{') depth++;
            else if (c == ')' || c == ']' || c == '}') depth--;
            else if (depth == 0) {
                if (c == '+' || c == '-' || c == '*' || c == '/' || c == '<' || c == '>' || c == '!' || c == '&' || c == '|' || c == '^' || c == '%') {
                    if (i + 1 < s.length() && s.charAt(i + 1) == '=') return null;
                }
                if (c == '=') {
                    if (i + 1 < s.length() && s.charAt(i + 1) == '=') { i++; continue; }
                    eqIdx = i;
                    break;
                }
            }
        }

        String lhs = (eqIdx >= 0 ? s.substring(0, eqIdx) : s).trim();
        if (lhs.isEmpty() || lhs.contains("(") || lhs.contains(".")) return null;

        /* Extract leading modifiers (`public`, `private`, `static`, `final` -> `const`, etc.) */
        StringBuilder mods = new StringBuilder();
        boolean isPublicStaticFinal = false;
        if (lhs.startsWith("public static final ")) {
            isPublicStaticFinal = true;
        }
        while (true) {
            int sp = lhs.indexOf(' ');
            if (sp <= 0) break;
            String tok = lhs.substring(0, sp);
            if (VAR_MODIFIERS.contains(tok)) {
                if (mods.length() > 0) mods.append(' ');
                mods.append(tok.equals("final") ? "const" : tok);
                lhs = lhs.substring(sp + 1).trim();
            } else {
                break;
            }
        }

        String trailingBrackets = "";
        while (lhs.endsWith("[]")) {
            trailingBrackets = "[]" + trailingBrackets;
            lhs = lhs.substring(0, lhs.length() - 2).trim();
        }

        int nameEnd = lhs.length();
        int nameStart = nameEnd;
        while (nameStart > 0 && isIdentCont(lhs.charAt(nameStart - 1))) nameStart--;
        if (nameStart == 0 || nameStart == nameEnd) return null;

        String varName = lhs.substring(nameStart, nameEnd);
        String typePart = lhs.substring(0, nameStart).trim() + trailingBrackets;
        if (typePart.isEmpty()) return null;

        /* Validate typePart characters */
        for (int i = 0; i < typePart.length(); i++) {
            char c = typePart.charAt(i);
            if (!isIdentCont(c) && c != ' ' && c != '<' && c != '>' && c != '[' && c != ']' && c != ',' && c != '.') {
                return null;
            }
        }

        String rhs = (eqIdx >= 0) ? s.substring(eqIdx + 1).trim() : null;

        /* Check if `public static final <prim/String> MAX_ITEMS = 64` at class/root scope should fold to `MAX_ITEMS = 64` */
        if (inClassScope && isPublicStaticFinal && rhs != null && isAllCapsIdent(varName) &&
            (typePart.equals("int") || typePart.equals("long") || typePart.equals("double") ||
             typePart.equals("boolean") || typePart.equals("String") || typePart.equals("char"))) {
            return varName + " = " + translateTokensJavaToMagma(rhs);
        }

        /* Check if `T[] arr = new T[N]` (sized array allocation) should fold to `arr: T[N]` */
        if (rhs != null && typePart.endsWith("[]") && rhs.startsWith("new ") && rhs.endsWith("]")) {
            String elemJavaType = typePart;
            int bracketCount = 0;
            while (elemJavaType.endsWith("[]")) {
                bracketCount++;
                elemJavaType = elemJavaType.substring(0, elemJavaType.length() - 2).trim();
            }
            String afterNew = rhs.substring(4).trim();
            if (afterNew.startsWith(elemJavaType + "[")) {
                String dimsPart = afterNew.substring(elemJavaType.length()).trim();
                StringBuilder magDims = new StringBuilder();
                int idx = 0;
                int dimCount = 0;
                while (idx < dimsPart.length() && dimsPart.charAt(idx) == '[') {
                    int cb = findMatchingDelim(dimsPart, idx, '[', ']');
                    if (cb >= dimsPart.length()) { dimCount = -1; break; }
                    String dExpr = dimsPart.substring(idx + 1, cb).trim();
                    if (dExpr.isEmpty()) { dimCount = -1; break; }
                    magDims.append('[').append(translateTokensJavaToMagma(dExpr)).append(']');
                    dimCount++;
                    idx = cb + 1;
                }
                if (dimCount == bracketCount && idx == dimsPart.length()) {
                    String prefix = mods.length() > 0 ? mods + " " : "";
                    return prefix + varName + ": " + translateTypeJavaToMagma(elemJavaType) + magDims;
                }
            }
        }

        StringBuilder out = new StringBuilder();
        if (mods.length() > 0) out.append(mods).append(' ');
        out.append(varName).append(": ").append(translateTypeJavaToMagma(typePart));
        if (rhs != null) {
            out.append(" = ").append(translateTokensJavaToMagma(rhs));
        }
        return out.toString();
    }

    private record ForLoopInfo(String magmaClause, String loopVar) {}

    /* Convert Java 3-clause `for (int i = start; i < stop; i++)` into `i in range(...)` */
    private static ForLoopInfo tryEmitJavaForRangeToMagma(String initS, String condS, String stepS) {
        String init = initS.trim();
        String cond = condS.trim();
        String step = stepS.trim();

        int eq = init.indexOf('=');
        if (eq <= 0) return null;
        String lhs = init.substring(0, eq).trim();
        String startS = init.substring(eq + 1).trim();
        if (lhs.isEmpty() || startS.isEmpty()) return null;

        int vEnd = lhs.length();
        int vStart = vEnd;
        while (vStart > 0 && isIdentCont(lhs.charAt(vStart - 1))) vStart--;
        if (vStart == 0 || vStart == vEnd) return null;

        String vname = lhs.substring(vStart, vEnd);
        String typeStr = lhs.substring(0, vStart).trim();
        if (typeStr.isEmpty()) return null;

        if (!cond.startsWith(vname) || cond.contains("&&") || cond.contains("||")) return null;
        String afterVar = cond.substring(vname.length()).trim();
        if (afterVar.isEmpty() || (afterVar.charAt(0) != '<' && afterVar.charAt(0) != '>')) return null;
        char cmpOp = afterVar.charAt(0);
        if (afterVar.length() > 1 && afterVar.charAt(1) == '=') return null;
        String stopS = afterVar.substring(1).trim();
        if (stopS.isEmpty()) return null;

        String customStep = null;
        boolean negStep = false;
        if (step.equals(vname + "++") || step.equals("++" + vname)) {
            if (cmpOp != '<') return null;
        } else if (step.equals(vname + "--") || step.equals("--" + vname)) {
            if (cmpOp != '>') return null;
            customStep = "-1";
            negStep = true;
        } else if (step.startsWith(vname)) {
            String stRest = step.substring(vname.length()).trim();
            if (stRest.startsWith("+=") || stRest.startsWith("-=")) {
                negStep = stRest.startsWith("-=");
                if ((negStep && cmpOp != '>') || (!negStep && cmpOp != '<')) return null;
                customStep = stRest.substring(2).trim();
                if (customStep.isEmpty()) return null;
            } else {
                return null;
            }
        } else {
            return null;
        }

        StringBuilder sb = new StringBuilder(vname);
        if (!typeStr.equals("int")) {
            sb.append(": ").append(translateTypeJavaToMagma(typeStr));
        }
        sb.append(" in range(");
        if (startS.equals("0") && customStep == null) {
            sb.append(translateTokensJavaToMagma(stopS));
        } else {
            sb.append(translateTokensJavaToMagma(startS)).append(", ").append(translateTokensJavaToMagma(stopS));
            if (customStep != null) {
                sb.append(", ");
                if (negStep && !customStep.startsWith("-")) sb.append('-');
                sb.append(translateTokensJavaToMagma(customStep));
            }
        }
        sb.append(')');
        return new ForLoopInfo(sb.toString(), vname);
    }

    /* Convert Java enhanced `for (var x : iter)` or `for (T x : iter)` into `x in iter` */
    private static ForLoopInfo tryEmitJavaForInToMagma(String condRaw) {
        String cond = condRaw.trim();
        int colonIdx = -1;
        int depth = 0;
        char quote = 0;
        for (int i = 0; i < cond.length(); i++) {
            char c = cond.charAt(i);
            if (quote != 0) {
                if (c == '\\' && i + 1 < cond.length()) i++;
                else if (c == quote) quote = 0;
                continue;
            }
            if (c == '"' || c == '\'') quote = c;
            else if (c == '(' || c == '[' || c == '{' || c == '<') depth++;
            else if (c == ')' || c == ']' || c == '}' || c == '>') depth--;
            else if (depth == 0 && c == ':') {
                colonIdx = i;
                break;
            }
        }
        if (colonIdx <= 0) return null;

        String lhs = cond.substring(0, colonIdx).trim();
        String rhs = cond.substring(colonIdx + 1).trim();
        if (lhs.isEmpty() || rhs.isEmpty()) return null;

        int vEnd = lhs.length();
        int vStart = vEnd;
        while (vStart > 0 && isIdentCont(lhs.charAt(vStart - 1))) vStart--;
        if (vStart == 0 || vStart == vEnd) return null;

        String vname = lhs.substring(vStart, vEnd);
        String typeStr = lhs.substring(0, vStart).trim();
        if (typeStr.isEmpty()) return null;

        StringBuilder sb = new StringBuilder(vname);
        if (!typeStr.equals("var")) {
            sb.append(": ").append(translateTypeJavaToMagma(typeStr));
        }
        sb.append(" in ").append(translateTokensJavaToMagma(rhs));
        return new ForLoopInfo(sb.toString(), vname);
    }

    private static String nextTrimmedJavaLine(String src, int[] cursor) {
        int p = cursor[0];
        int len = src.length();
        if (p >= len) return null;
        int ls = p;
        while (p < len && src.charAt(p) != '\n' && src.charAt(p) != '\r') p++;
        int le = p;
        if (p < len) {
            if (src.charAt(p) == '\r' && p + 1 < len && src.charAt(p + 1) == '\n') p += 2;
            else p++;
        }
        cursor[0] = p;
        return src.substring(ls, le).trim();
    }

    /* Fold a Java array/collection declaration + initialization loop back into a Magma comprehension */
    private static String tryEmitJavaComprehensionToMagma(String declLine, String src, int[] ioCursor) {
        int eqIdx = declLine.indexOf('=');
        if (eqIdx <= 0) return null;

        String lhs = declLine.substring(0, eqIdx).trim();
        String rhs = declLine.substring(eqIdx + 1).trim();
        if (lhs.isEmpty() || rhs.isEmpty() || lhs.contains("(")) return null;

        int nameEnd = lhs.length();
        int nameStart = nameEnd;
        while (nameStart > 0 && isIdentCont(lhs.charAt(nameStart - 1))) nameStart--;
        if (nameStart == 0 || nameStart == nameEnd) return null;

        String varName = lhs.substring(nameStart, nameEnd);
        String javaType = lhs.substring(0, nameStart).trim();
        if (javaType.isEmpty()) return null;

        boolean isJavaArray = javaType.endsWith("[]") && rhs.startsWith("new ") && rhs.endsWith("]");
        boolean isBoolArray = isJavaArray && javaType.equals("boolean[]");
        boolean isJavaList = javaType.startsWith("ArrayList<") && rhs.equals("new ArrayList<>()");
        boolean isJavaSet = (javaType.startsWith("TreeSet<") && rhs.equals("new TreeSet<>()")) ||
                            (javaType.startsWith("HashSet<") && rhs.equals("new HashSet<>()"));
        boolean isJavaMap = (javaType.startsWith("TreeMap<") && rhs.equals("new TreeMap<>()")) ||
                            (javaType.startsWith("HashMap<") && rhs.equals("new HashMap<>()"));

        if (!isJavaArray && !isJavaList && !isJavaSet && !isJavaMap) return null;

        String magmaDeclType;
        if (isJavaArray) {
            String elemType = javaType.substring(0, javaType.length() - 2).trim();
            String afterNew = rhs.substring(4).trim();
            if (!afterNew.startsWith(elemType + "[")) return null;
            String dimPart = afterNew.substring(elemType.length()).trim();
            int cb = findMatchingDelim(dimPart, 0, '[', ']');
            if (cb != dimPart.length() - 1) return null;
            String dimExpr = dimPart.substring(1, cb).trim();
            magmaDeclType = translateTypeJavaToMagma(elemType) + "[" + translateTokensJavaToMagma(dimExpr) + "]";
        } else {
            magmaDeclType = translateTypeJavaToMagma(javaType);
        }

        int[] scan = new int[]{ioCursor[0]};
        String forLine = nextTrimmedJavaLine(src, scan);
        if (forLine == null || !forLine.endsWith("{")) return null;
        int kwAfter = startsWithKw(forLine.substring(0, forLine.length() - 1).trim(), "for");
        if (kwAfter < 0) return null;
        String forCond = forLine.substring(0, forLine.length() - 1).trim().substring(kwAfter).trim();
        if (forCond.length() < 2 || forCond.charAt(0) != '(' || forCond.charAt(forCond.length() - 1) != ')') return null;
        forCond = forCond.substring(1, forCond.length() - 1).trim();

        ForLoopInfo forInfo;
        int semi1 = forCond.indexOf(';');
        int semi2 = (semi1 >= 0) ? forCond.indexOf(';', semi1 + 1) : -1;
        if (semi1 >= 0 && semi2 > semi1) {
            forInfo = tryEmitJavaForRangeToMagma(
                forCond.substring(0, semi1),
                forCond.substring(semi1 + 1, semi2),
                forCond.substring(semi2 + 1)
            );
        } else {
            forInfo = tryEmitJavaForInToMagma(forCond);
        }
        if (forInfo == null) return null;

        String line2 = nextTrimmedJavaLine(src, scan);
        if (line2 == null || line2.isEmpty()) return null;

        String ifCond = null;
        String stmtLine = line2;
        if (line2.endsWith("{")) {
            String h2 = line2.substring(0, line2.length() - 1).trim();
            int ifAfter = startsWithKw(h2, "if");
            if (ifAfter < 0) return null;
            ifCond = h2.substring(ifAfter).trim();
            if (ifCond.length() < 2 || ifCond.charAt(0) != '(' || ifCond.charAt(ifCond.length() - 1) != ')') return null;
            ifCond = ifCond.substring(1, ifCond.length() - 1).trim();
            stmtLine = nextTrimmedJavaLine(src, scan);
            if (stmtLine == null || stmtLine.isEmpty()) return null;
        }

        if (!stmtLine.endsWith(";")) return null;
        stmtLine = stmtLine.substring(0, stmtLine.length() - 1).trim();

        if (ifCond != null) {
            String closeIf = nextTrimmedJavaLine(src, scan);
            if (!"}".equals(closeIf)) return null;
        }
        String closeFor = nextTrimmedJavaLine(src, scan);
        if (!"}".equals(closeFor)) return null;

        if (!stmtLine.startsWith(varName)) return null;
        String afterVar = stmtLine.substring(varName.length());

        CompKind kind = CompKind.LIST;
        String keyStr = null;
        String elemStr = null;
        boolean matched = false;

        if (isJavaList && afterVar.startsWith(".add(") && afterVar.endsWith(")")) {
            kind = CompKind.LIST;
            elemStr = afterVar.substring(5, afterVar.length() - 1).trim();
            matched = true;
        } else if (isJavaSet && afterVar.startsWith(".add(") && afterVar.endsWith(")")) {
            kind = CompKind.SET;
            elemStr = afterVar.substring(5, afterVar.length() - 1).trim();
            matched = true;
        } else if (isJavaMap && afterVar.startsWith(".put(") && afterVar.endsWith(")")) {
            List<String> kv = splitTopLevelCommas(afterVar.substring(5, afterVar.length() - 1));
            if (kv.size() == 2) {
                kind = CompKind.DICT;
                keyStr = kv.get(0);
                elemStr = kv.get(1);
                matched = true;
            }
        } else if (isJavaArray && afterVar.startsWith("[")) {
            int cb = findMatchingDelim(afterVar, 0, '[', ']');
            if (cb > 1 && cb + 1 < afterVar.length()) {
                String idxS = afterVar.substring(1, cb).trim();
                String rest = afterVar.substring(cb + 1).trim();
                if (rest.startsWith("=") && !rest.startsWith("==")) {
                    String valS = rest.substring(1).trim();
                    if (isBoolArray && valS.equals("true")) {
                        kind = CompKind.SET;
                        elemStr = idxS;
                        matched = true;
                    } else if (!isBoolArray && ifCond == null && idxS.equals(forInfo.loopVar())) {
                        kind = CompKind.LIST;
                        elemStr = valS;
                        matched = true;
                    } else {
                        kind = CompKind.DICT;
                        keyStr = idxS;
                        elemStr = valS;
                        matched = true;
                    }
                }
            }
        }

        if (!matched || elemStr == null || elemStr.isEmpty()) return null;

        StringBuilder out = new StringBuilder();
        out.append(varName).append(": ").append(magmaDeclType).append(" = ");
        out.append(kind == CompKind.LIST ? '[' : '{');
        if (kind == CompKind.DICT) {
            out.append(translateTokensJavaToMagma(keyStr)).append(": ");
        }
        out.append(translateTokensJavaToMagma(elemStr))
           .append(" for ")
           .append(forInfo.magmaClause());
        if (ifCond != null) {
            out.append(" if ").append(translateTokensJavaToMagma(ifCond));
        }
        out.append(kind == CompKind.LIST ? ']' : '}');

        ioCursor[0] = scan[0];
        return out.toString();
    }

    private static String transformClassHeaderJavaToMagma(String header) {
        String h = header.trim();
        addTag(h);

        /* Record header `record Vec2(double x, double y)` -> `record Vec2(x: f64, y: f64)` */
        int recIdx = h.indexOf("record ");
        if (recIdx >= 0) {
            int lp = h.indexOf('(', recIdx);
            int rp = (lp >= 0) ? findMatchingParen(h, lp) : -1;
            if (lp > 0 && rp > lp) {
                String before = h.substring(0, lp).trim();
                List<String> rparams = splitTopLevelCommas(h.substring(lp + 1, rp));
                StringBuilder pstr = new StringBuilder();
                for (int i = 0; i < rparams.size(); i++) {
                    if (rparams.get(i).isEmpty()) continue;
                    if (pstr.length() > 0) pstr.append(", ");
                    pstr.append(emitMagmaParam(rparams.get(i)));
                }
                String after = h.substring(rp + 1).trim();
                return translateTokensJavaToMagma(before) + "(" + pstr + ")" +
                       (after.isEmpty() ? "" : " " + translateTokensJavaToMagma(after));
            }
        }

        /* `class Dog extends Animal` -> `class Dog(Animal)` */
        int extIdx = h.indexOf(" extends ");
        if (extIdx > 0 && (h.startsWith("class ") || h.contains(" class "))) {
            String before = h.substring(0, extIdx).trim();
            String afterExt = h.substring(extIdx + 9).trim();
            int implIdx = afterExt.indexOf(" implements ");
            if (implIdx > 0) {
                String base = afterExt.substring(0, implIdx).trim();
                String implPart = afterExt.substring(implIdx).trim();
                return translateTokensJavaToMagma(before) + "(" + translateTypeJavaToMagma(base) + ") " +
                       translateTokensJavaToMagma(implPart);
            } else {
                return translateTokensJavaToMagma(before) + "(" + translateTypeJavaToMagma(afterExt) + ")";
            }
        }

        return translateTokensJavaToMagma(h);
    }

    public static String magmaFromJavaIndent(String src, String indentUnit) throws MagmaException {
        String unit = (indentUnit != null) ? indentUnit : "    ";
        if (!isValidIndentUnit(unit)) {
            throw new MagmaException("invalid indent unit", 1, 1);
        }

        resetSymtab();
        StringBuilder out = new StringBuilder(src.length() + 128);

        int depth = 0;
        boolean inCaseBody = false;
        int caseSwitchDepth = 0;
        List<BlockFrame> blockStack = new ArrayList<>();

        int[] cursor = new int[]{0};
        int len = src.length();

        while (cursor[0] < len) {
            int ls = cursor[0];
            int p = ls;
            while (p < len && src.charAt(p) != '\n' && src.charAt(p) != '\r') p++;
            int le = p;
            if (p < len) {
                if (src.charAt(p) == '\r' && p + 1 < len && src.charAt(p + 1) == '\n') p += 2;
                else p++;
            }
            cursor[0] = p;

            String line = src.substring(ls, le).trim();
            if (line.isEmpty()) {
                out.append('\n');
                continue;
            }

            /* Single-line `//` comment -> `#` comment */
            if (line.startsWith("//")) {
                int effDepth = depth + (inCaseBody ? 1 : 0);
                appendIndent(out, unit, effDepth);
                out.append('#').append(line.substring(2)).append('\n');
                continue;
            }

            /* Split trailing `//` comment outside string/char literals */
            String inlineComment = null;
            int codeLen = line.length();
            char quote = 0;
            for (int i = 0; i + 1 < line.length(); i++) {
                char c = line.charAt(i);
                if (quote != 0) {
                    if (c == '\\') i++;
                    else if (c == quote) quote = 0;
                    continue;
                }
                if (c == '"' || c == '\'') { quote = c; continue; }
                if (c == '/' && line.charAt(i + 1) == '/') {
                    inlineComment = line.substring(i + 2);
                    codeLen = i;
                    while (codeLen > 0 && line.charAt(codeLen - 1) == ' ') codeLen--;
                    break;
                }
            }
            line = line.substring(0, codeLen);

            /* Handle leading `}` (`}`, `};`, `} else if (...) {`, `} else {`, `} catch (...) {`, `} finally {`, `} while (...);`) */
            if (line.startsWith("}")) {
                if (inCaseBody && depth == caseSwitchDepth) {
                    inCaseBody = false;
                }
                if (depth > 0) depth--;
                if (!blockStack.isEmpty()) blockStack.remove(blockStack.size() - 1);

                String rest = line.substring(1).trim();
                if (rest.isEmpty() || rest.equals(";")) {
                    continue;
                }
                line = rest;
            }

            int kwAfter;
            if ((kwAfter = startsWithKw(line, "case")) >= 0 || line.equals("default:")) {
                inCaseBody = false;
                appendIndent(out, unit, depth);
                out.append(translateTokensJavaToMagma(line));
                if (inlineComment != null) out.append(" #").append(inlineComment);
                out.append('\n');
                inCaseBody = true;
                caseSwitchDepth = depth;
                continue;
            }

            int effDepth = depth + (inCaseBody ? 1 : 0);

            /* Single-line empty record `record Vec2(double x, double y) {}` */
            if (line.endsWith("{}") && (line.startsWith("record ") || line.contains(" record "))) {
                String rhead = line.substring(0, line.length() - 2).trim();
                appendIndent(out, unit, effDepth);
                out.append(transformClassHeaderJavaToMagma(rhead));
                if (inlineComment != null) out.append(" #").append(inlineComment);
                out.append('\n');
                continue;
            }

            /* Block header ending with `{` */
            if (line.endsWith("{")) {
                String header = line.substring(0, line.length() - 1).trim();
                appendIndent(out, unit, effDepth);
                BlockKind pushedKind = BlockKind.NORMAL;

                if ((kwAfter = startsWithKw(header, "else if")) >= 0) {
                    String cond = header.substring(kwAfter).trim();
                    if (cond.length() >= 2 && cond.charAt(0) == '(' && cond.charAt(cond.length() - 1) == ')') {
                        cond = cond.substring(1, cond.length() - 1).trim();
                    }
                    out.append("elif ").append(translateTokensJavaToMagma(cond)).append(':');
                } else if (header.equals("else")) {
                    out.append("else:");
                } else if ((kwAfter = startsWithKw(header, "catch")) >= 0) {
                    String cexpr = header.substring(kwAfter).trim();
                    if (cexpr.length() >= 2 && cexpr.charAt(0) == '(' && cexpr.charAt(cexpr.length() - 1) == ')') {
                        cexpr = cexpr.substring(1, cexpr.length() - 1).trim();
                    }
                    out.append("catch (").append(emitMagmaParam(cexpr)).append("):");
                } else if (header.equals("finally")) {
                    out.append("finally:");
                } else if ((kwAfter = startsWithKw(header, "if")) >= 0) {
                    String cond = header.substring(kwAfter).trim();
                    if (cond.length() >= 2 && cond.charAt(0) == '(' && cond.charAt(cond.length() - 1) == ')') {
                        cond = cond.substring(1, cond.length() - 1).trim();
                    }
                    out.append("if ").append(translateTokensJavaToMagma(cond)).append(':');
                } else if ((kwAfter = startsWithKw(header, "while")) >= 0) {
                    String cond = header.substring(kwAfter).trim();
                    if (cond.length() >= 2 && cond.charAt(0) == '(' && cond.charAt(cond.length() - 1) == ')') {
                        cond = cond.substring(1, cond.length() - 1).trim();
                    }
                    out.append("while ").append(translateTokensJavaToMagma(cond)).append(':');
                } else if ((kwAfter = startsWithKw(header, "for")) >= 0) {
                    String cond = header.substring(kwAfter).trim();
                    if (cond.length() >= 2 && cond.charAt(0) == '(' && cond.charAt(cond.length() - 1) == ')') {
                        cond = cond.substring(1, cond.length() - 1).trim();
                    }
                    out.append("for ");
                    int semi1 = cond.indexOf(';');
                    int semi2 = (semi1 >= 0) ? cond.indexOf(';', semi1 + 1) : -1;
                    if (semi1 >= 0 && semi2 > semi1) {
                        String c1 = cond.substring(0, semi1).trim();
                        String c2 = cond.substring(semi1 + 1, semi2).trim();
                        String c3 = cond.substring(semi2 + 1).trim();
                        ForLoopInfo rangeInfo = tryEmitJavaForRangeToMagma(c1, c2, c3);
                        if (rangeInfo != null) {
                            out.append(rangeInfo.magmaClause());
                        } else {
                            String vdecl = tryEmitJavaVarDeclToMagma(c1, false);
                            out.append(vdecl != null ? vdecl : translateTokensJavaToMagma(c1))
                               .append("; ")
                               .append(translateTokensJavaToMagma(c2))
                               .append("; ")
                               .append(translateTokensJavaToMagma(c3));
                        }
                    } else {
                        ForLoopInfo inInfo = tryEmitJavaForInToMagma(cond);
                        out.append(inInfo != null ? inInfo.magmaClause() : translateTokensJavaToMagma(cond));
                    }
                    out.append(':');
                } else if ((kwAfter = startsWithKw(header, "switch")) >= 0) {
                    String cond = header.substring(kwAfter).trim();
                    if (cond.length() >= 2 && cond.charAt(0) == '(' && cond.charAt(cond.length() - 1) == ')') {
                        cond = cond.substring(1, cond.length() - 1).trim();
                    }
                    out.append("switch ").append(translateTokensJavaToMagma(cond)).append(':');
                    pushedKind = BlockKind.SWITCH;
                } else if (header.startsWith("enum ") || header.contains(" enum ")) {
                    addTag(header);
                    out.append(translateTokensJavaToMagma(header)).append(':');
                    pushedKind = BlockKind.ENUM;
                } else if (header.startsWith("class ") || header.contains(" class ") ||
                           header.startsWith("interface ") || header.contains(" interface ") ||
                           header.startsWith("record ") || header.contains(" record ")) {
                    out.append(transformClassHeaderJavaToMagma(header)).append(':');
                    pushedKind = BlockKind.CLASS_OR_INTERFACE;
                } else {
                    String fnMagma = tryEmitJavaFuncToMagma(header, true);
                    if (fnMagma != null) {
                        out.append(fnMagma);
                    } else {
                        out.append(translateTokensJavaToMagma(header)).append(':');
                    }
                }

                if (inlineComment != null) out.append(" #").append(inlineComment);
                out.append('\n');
                blockStack.add(new BlockFrame(effDepth, pushedKind));
                depth++;
                continue;
            }

            /* Strip trailing `;` (or trailing `,` inside an `enum` block) */
            boolean inEnumScope = !blockStack.isEmpty() && blockStack.get(blockStack.size() - 1).kind() == BlockKind.ENUM;
            if (inEnumScope && line.endsWith(",")) {
                line = line.substring(0, line.length() - 1).trim();
            } else if (line.endsWith(";")) {
                line = line.substring(0, line.length() - 1).trim();
            }

            appendIndent(out, unit, effDepth);

            boolean inClassScope = (effDepth == 0) ||
                (!blockStack.isEmpty() && blockStack.get(blockStack.size() - 1).kind() == BlockKind.CLASS_OR_INTERFACE);

            String fnProto = tryEmitJavaFuncToMagma(line, false);
            if (fnProto != null) {
                out.append(fnProto);
            } else {
                String compMagma = (inlineComment == null) ? tryEmitJavaComprehensionToMagma(line, src, cursor) : null;
                if (compMagma != null) {
                    out.append(compMagma);
                } else {
                    String varMagma = tryEmitJavaVarDeclToMagma(line, inClassScope);
                    if (varMagma != null) {
                        out.append(varMagma);
                    } else {
                        out.append(translateTokensJavaToMagma(line));
                    }
                }
            }

            if (inlineComment != null) out.append(" #").append(inlineComment);
            out.append('\n');
        }

        return out.toString();
    }

    public static String magmaFormatIndent(String src, String indentUnit) throws MagmaException {
        String javaCode = magmaToJava(src);
        return magmaFromJavaIndent(javaCode, indentUnit);
    }

    /* -------------------------------------------------------------------------
     * Java Compilation, Packaging, & Execution Helpers (`--compile` / `--run`)
     * ------------------------------------------------------------------------- */

    private static String findPrimaryClassName(String javaCode) {
        String firstClass = null;
        for (String rawLine : javaCode.split("\\R")) {
            String line = rawLine.trim();
            if (line.startsWith("//")) continue;
            if (line.startsWith("public class ") || line.startsWith("class ")) {
                String rest = line.startsWith("public class ")
                    ? line.substring("public class ".length()).trim()
                    : line.substring("class ".length()).trim();
                int end = 0;
                while (end < rest.length() && isIdentCont(rest.charAt(end))) end++;
                if (end > 0) {
                    String cname = rest.substring(0, end);
                    if (line.startsWith("public class ")) return cname;
                    if (firstClass == null) firstClass = cname;
                }
            }
        }
        return firstClass;
    }

    private static void deleteDirRecursive(Path dir) {
        try (var stream = Files.walk(dir)) {
            stream.sorted(Comparator.reverseOrder()).map(Path::toFile).forEach(File::delete);
        } catch (IOException ignored) {
        }
    }

    private static int compileOrRunJava(String javaCode, String outputBin, boolean runMode) {
        Path tempDir = null;
        try {
            tempDir = Files.createTempDirectory("magma_build_");
            String mainClass = findPrimaryClassName(javaCode);
            if (mainClass == null) {
                mainClass = "MagmaMain";
                javaCode = "import java.util.*;\npublic class MagmaMain {\n" + javaCode + "\n}\n";
            }

            Path srcFile = tempDir.resolve(mainClass + ".java");
            Files.writeString(srcFile, javaCode, StandardCharsets.UTF_8);

            JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
            int rc;
            if (compiler != null) {
                rc = compiler.run(null, null, null, "-d", tempDir.toString(), srcFile.toString());
            } else {
                Process p = new ProcessBuilder("javac", "-d", tempDir.toString(), srcFile.toString())
                    .inheritIO().start();
                rc = p.waitFor();
            }
            if (rc != 0) return 1;

            if (runMode && outputBin == null) {
                Process runProc = new ProcessBuilder("java", "-cp", tempDir.toString(), mainClass)
                    .inheritIO().start();
                return runProc.waitFor();
            }

            /* Package compiled `.class` files into an executable JAR / self-executing binary */
            String targetPath = (outputBin != null) ? outputBin : mainClass.toLowerCase();
            Path jarFile = tempDir.resolve("app.jar");
            Manifest manifest = new Manifest();
            manifest.getMainAttributes().put(Attributes.Name.MANIFEST_VERSION, "1.0");
            manifest.getMainAttributes().put(Attributes.Name.MAIN_CLASS, mainClass);

            try (JarOutputStream jos = new JarOutputStream(new FileOutputStream(jarFile.toFile()), manifest);
                 var walk = Files.walk(tempDir)) {
                List<Path> classFiles = walk.filter(p -> p.toString().endsWith(".class")).toList();
                for (Path cf : classFiles) {
                    String entryName = tempDir.relativize(cf).toString().replace('\\', '/');
                    jos.putNextEntry(new JarEntry(entryName));
                    Files.copy(cf, jos);
                    jos.closeEntry();
                }
            }

            File outFile = new File(targetPath);
            try (FileOutputStream fos = new FileOutputStream(outFile)) {
                if (!targetPath.endsWith(".jar")) {
                    byte[] stub = "#!/bin/sh\nexec java -jar \"$0\" \"$@\"\n".getBytes(StandardCharsets.UTF_8);
                    fos.write(stub);
                }
                Files.copy(jarFile, fos);
            }
            outFile.setExecutable(true, false);

            if (runMode) {
                Process runProc = new ProcessBuilder(outFile.getAbsolutePath()).inheritIO().start();
                return runProc.waitFor();
            }
            return 0;
        } catch (Exception e) {
            System.err.println("magma error: " + e.getMessage());
            return 1;
        } finally {
            if (tempDir != null) deleteDirRecursive(tempDir);
        }
    }

    /* -------------------------------------------------------------------------
     * Conformance Test Suite & Throughput Benchmark
     * ------------------------------------------------------------------------- */

    private static int runTests() {
        String[] magmaCases = {
            /* Case 0: Classes, constants, casts, range loops, logical operators */
            "import java.util.ArrayList\n" +
            "\n" +
            "class Point:\n" +
            "    x: f64\n" +
            "    y: f64\n" +
            "\n" +
            "public class Demo:\n" +
            "    MAX_ITEMS = 64\n" +
            "\n" +
            "    static def move_x(p: Point, dx: f64):\n" +
            "        p.x += dx\n" +
            "\n" +
            "    static def clamp(val: i32, lo: i32, hi: i32) -> i32:\n" +
            "        if val < lo:\n" +
            "            return lo\n" +
            "        elif val > hi:\n" +
            "            return hi\n" +
            "        else:\n" +
            "            return val\n" +
            "\n" +
            "    public static def main(args: str[]):\n" +
            "        pt: Point = new Point()\n" +
            "        pt.x = f64(1)\n" +
            "        raw: any = pt\n" +
            "        move_x(cast(Point, raw), 2.5)\n" +
            "        total: i32 = 0\n" +
            "        for i in range(10):\n" +
            "            if i == 5 and not (total < 0):\n" +
            "                total += clamp(i, 0, MAX_ITEMS)\n" +
            "        printf(\"total=%d\\n\", total)\n",

            /* Case 1: Tab-indented with enum, switch/case, arrays, and methods */
            "enum Status:\n" +
            "\tOK\n" +
            "\tERR\n" +
            "\n" +
            "public class Checker:\n" +
            "\tstatic def check(argv: str[], out_code: Status[], code: i32) -> bool:\n" +
            "\t\tif argv == nil or argv.length == 0 or code != 0:\n" +
            "\t\t\tout_code[0] = Status.ERR\n" +
            "\t\t\treturn false\n" +
            "\t\tswitch code:\n" +
            "\t\t\tcase 0:\n" +
            "\t\t\t\tout_code[0] = Status.OK\n" +
            "\t\t\t\treturn true\n" +
            "\t\t\tdefault:\n" +
            "\t\t\t\treturn false\n",

            /* Case 2: List, set, and dict comprehensions (Java fixed-size arrays & Java collections) */
            "import java.util.ArrayList\n" +
            "import java.util.TreeSet\n" +
            "import java.util.TreeMap\n" +
            "\n" +
            "public class CompTest:\n" +
            "    static def test_comprehensions() -> i32:\n" +
            "        squares: i32[8] = [i * i for i in range(8)]\n" +
            "        evens: bool[16] = {i for i in range(16) if i % 2 == 0}\n" +
            "        table: i32[8] = {i: i * 10 for i in range(8) if i > 0}\n" +
            "        vec: list[i32] = [x * 2 for x in squares if x > 0]\n" +
            "        uniq: set[i32] = {x for x in vec}\n" +
            "        mapping: dict[i32, i32] = {x: x + 1 for x in uniq if x < 100}\n" +
            "        return table[2] + squares[3]\n"
        };

        String[] indents = {"  ", "    ", "\t"};
        int passed = 0;

        for (int i = 0; i < magmaCases.length; i++) {
            for (String indent : indents) {
                try {
                    String j1 = magmaToJava(magmaCases[i]);
                    String mg = magmaFromJavaIndent(j1, indent);
                    String j2 = magmaToJava(mg);
                    if (!j1.equals(j2)) {
                        System.err.printf("FAIL [case %d roundtrip mismatch]\n--- Expected Java ---\n%s--- Got Java ---\n%s",
                                          i, j1, j2);
                        return 1;
                    }
                    passed++;
                } catch (MagmaException e) {
                    System.err.printf("FAIL [case %d]: %s (line %d)\n", i, e.getMessage(), e.line);
                    return 1;
                }
            }
        }

        /* Universal newlines test (\r\n and \r) */
        try {
            String crlfSrc = "def add(a: i32, b: i32) -> i32:\r\n    return a + b\r";
            String jOut = magmaToJava(crlfSrc);
            String expected = "int add(int a, int b) {\n    return a + b;\n}\n";
            if (!jOut.equals(expected)) {
                System.err.printf("FAIL [universal_newlines output]:\nGot:\n%sExpected:\n%s", jOut, expected);
                return 1;
            }
            passed++;
        } catch (MagmaException e) {
            System.err.println("FAIL [universal_newlines]: " + e.getMessage());
            return 1;
        }

        /* Exact comprehension Java codegen & bidirectional round-trip test */
        try {
            String compMagma =
                "def demo():\n" +
                "    squares: i32[8] = [i * i for i in range(8)]\n" +
                "    evens: bool[16] = {i for i in range(16) if i % 2 == 0}\n" +
                "    table: i32[8] = {i: i * 10 for i in range(8) if i > 0}\n" +
                "    vec: list[i32] = [x * 2 for x in squares if x > 0]\n" +
                "    uniq: set[i32] = {x for x in vec}\n" +
                "    mapping: dict[i32, i32] = {x: x + 1 for x in uniq if x < 100}\n";
            String expectedJava =
                "void demo() {\n" +
                "    int[] squares = new int[8];\n" +
                "    for (int i = 0; i < 8; i++) {\n" +
                "        squares[i] = i * i;\n" +
                "    }\n" +
                "    boolean[] evens = new boolean[16];\n" +
                "    for (int i = 0; i < 16; i++) {\n" +
                "        if (i % 2 == 0) {\n" +
                "            evens[i] = true;\n" +
                "        }\n" +
                "    }\n" +
                "    int[] table = new int[8];\n" +
                "    for (int i = 0; i < 8; i++) {\n" +
                "        if (i > 0) {\n" +
                "            table[i] = i * 10;\n" +
                "        }\n" +
                "    }\n" +
                "    ArrayList<Integer> vec = new ArrayList<>();\n" +
                "    for (var x : squares) {\n" +
                "        if (x > 0) {\n" +
                "            vec.add(x * 2);\n" +
                "        }\n" +
                "    }\n" +
                "    TreeSet<Integer> uniq = new TreeSet<>();\n" +
                "    for (var x : vec) {\n" +
                "        uniq.add(x);\n" +
                "    }\n" +
                "    TreeMap<Integer, Integer> mapping = new TreeMap<>();\n" +
                "    for (var x : uniq) {\n" +
                "        if (x < 100) {\n" +
                "            mapping.put(x, x + 1);\n" +
                "        }\n" +
                "    }\n" +
                "}\n";
            String jOut = magmaToJava(compMagma);
            if (!jOut.equals(expectedJava)) {
                System.err.printf("FAIL [comprehensions Java output]\n--- Expected ---\n%s--- Got ---\n%s",
                                  expectedJava, jOut);
                return 1;
            }
            String mgOut = magmaFromJavaIndent(jOut, "    ");
            if (!mgOut.equals(compMagma)) {
                System.err.printf("FAIL [comprehensions Magma roundtrip]\n--- Expected ---\n%s--- Got ---\n%s",
                                  compMagma, mgOut);
                return 1;
            }
            passed++;
        } catch (MagmaException e) {
            System.err.printf("FAIL [comprehensions]: %s (line %d)\n", e.getMessage(), e.line);
            return 1;
        }

        /* Invalid syntax tests */
        String[] invalidCases = {
            "    x: i32 = 1\n",                        /* Unexpected root indent */
            "def foo():\n    x: i32 = 1\n  y: i32 = 2\n", /* Inconsistent indent multiple */
            "def foo():\n\tx: i32 = 1\n    y: i32 = 2\n", /* Mixed tab and space lines */
            "def foo():\n \tx: i32 = 1\n",             /* Mixed space+tab on same line */
            "def dangling():\n",                       /* Dangling block header at EOF */
            "def dangling():\nx: i32 = 1\n",           /* Missing indent after ':' */
            "x: i32 = 1   \n"                          /* Trailing whitespace */
        };
        for (int i = 0; i < invalidCases.length; i++) {
            try {
                magmaToJava(invalidCases[i]);
                System.err.printf("FAIL [invalid %d accepted]: %s\n", i, invalidCases[i]);
                return 1;
            } catch (MagmaException expected) {
                passed++;
            }
        }

        System.out.printf("Java Magma: all %d conformance tests passed.%n", passed);
        return 0;
    }

    private static int runBench(String path) {
        String mg4Sample;
        if (path != null) {
            try {
                mg4Sample = Files.readString(Path.of(path), StandardCharsets.UTF_8);
            } catch (IOException e) {
                System.err.println("magma error: cannot read '" + path + "'");
                return 1;
            }
        } else {
            StringBuilder b = new StringBuilder(65536);
            b.append("public class BenchModule:\n")
             .append("    static class Node:\n")
             .append("        id: i32\n")
             .append("        weight: f64\n")
             .append("        active: bool\n")
             .append("        label: str\n\n");
            for (int i = 0; i < 250; i++) {
                b.append(String.format(
                    "    static def compute_layer_%d(n: Node[], count: i32, threshold: f64) -> f64:\n" +
                    "        acc: f64 = 0.0\n" +
                    "        for i in range(count):\n" +
                    "            if n[i].active and n[i].weight > threshold:\n" +
                    "                acc += n[i].weight * 1.25\n" +
                    "            elif not n[i].active or n[i].id == %d:\n" +
                    "                acc -= 0.5\n" +
                    "            else:\n" +
                    "                acc += 0.1\n" +
                    "        return acc\n\n",
                    i, i
                ));
            }
            mg4Sample = b.toString();
        }

        try {
            String javaSample = magmaToJava(mg4Sample);
            String mgTabSample = magmaFromJavaIndent(javaSample, "\t");

            /* JIT warm-up */
            for (int i = 0; i < 200; i++) {
                magmaToJava(mg4Sample);
                magmaToJava(mgTabSample);
                magmaFromJavaIndent(javaSample, "    ");
            }

            int iters = 1000;
            long t0 = System.nanoTime();
            for (int i = 0; i < iters; i++) {
                magmaToJava(mg4Sample);
            }
            double dtMg4 = (System.nanoTime() - t0) * 1e-9;

            t0 = System.nanoTime();
            for (int i = 0; i < iters; i++) {
                magmaToJava(mgTabSample);
            }
            double dtTab = (System.nanoTime() - t0) * 1e-9;

            t0 = System.nanoTime();
            for (int i = 0; i < iters; i++) {
                magmaFromJavaIndent(javaSample, "    ");
            }
            double dtFromJava = (System.nanoTime() - t0) * 1e-9;

            int javaBytes = javaSample.getBytes(StandardCharsets.UTF_8).length;
            int mg4Bytes = mg4Sample.getBytes(StandardCharsets.UTF_8).length;
            int mgTabBytes = mgTabSample.getBytes(StandardCharsets.UTF_8).length;

            double mibMg4 = ((double) mg4Bytes * iters / (1024.0 * 1024.0)) / dtMg4;
            double mibTab = ((double) mgTabBytes * iters / (1024.0 * 1024.0)) / dtTab;
            double mibFromJava = ((double) javaBytes * iters / (1024.0 * 1024.0)) / dtFromJava;

            System.out.printf("Magma Benchmark (250 methods, %d iterations):%n", iters);
            System.out.printf("  Java source size       : %d bytes (%.1f KiB)%n",
                              javaBytes, javaBytes / 1024.0);
            System.out.printf("  Magma 4-space size     : %d bytes (%.1f KiB, %+.1f%% vs Java)%n",
                              mg4Bytes, mg4Bytes / 1024.0,
                              100.0 * (mg4Bytes - javaBytes) / javaBytes);
            System.out.printf("  Magma tab (\\t) size    : %d bytes (%.1f KiB, %+.1f%% vs Java)%n",
                              mgTabBytes, mgTabBytes / 1024.0,
                              100.0 * (mgTabBytes - javaBytes) / javaBytes);
            System.out.printf("  Magma (4-sp) -> Java   : %.0f files/s (%.1f MiB/s)%n",
                              iters / dtMg4, mibMg4);
            System.out.printf("  Magma (tab)  -> Java   : %.0f files/s (%.1f MiB/s)%n",
                              iters / dtTab, mibTab);
            System.out.printf("  Java -> Magma (4-sp)   : %.0f files/s (%.1f MiB/s)%n",
                              iters / dtFromJava, mibFromJava);
            return 0;
        } catch (MagmaException e) {
            System.err.printf("magma bench error: %s (line %d)%n", e.getMessage(), e.line);
            return 1;
        }
    }

    private static void printUsage() {
        System.err.println(
            "Usage:\n" +
            "  magma <file.mg>                           Transpile Magma to Java on stdout\n" +
            "  magma --magma [--indent <N|tab>] <f>      Format/canonicalize Magma\n" +
            "  magma --from-java [--indent <N|tab>] <f>  Convert Java source to Magma\n" +
            "  magma --compile <file.mg> [-o <bin>]      Transpile and compile via javac\n" +
            "  magma --run <file.mg>                     Transpile, compile, and execute immediately\n" +
            "  magma --check <file.mg>                   Validate Magma syntax only\n" +
            "  magma --test                              Run built-in conformance test suite\n" +
            "  magma --bench [file.mg]                   Run transpilation throughput benchmark"
        );
    }

    public static void main(String[] args) {
        if (args.length < 1) {
            printUsage();
            System.exit(1);
        }

        boolean modeMagma = false;
        boolean modeFromJava = false;
        boolean modeCheck = false;
        boolean modeCompile = false;
        boolean modeRun = false;
        String indentOpt = "    ";
        String inputPath = null;
        String outputBin = null;

        for (int i = 0; i < args.length; i++) {
            String arg = args[i];
            if (arg.equals("--test")) {
                System.exit(runTests());
            } else if (arg.equals("--bench")) {
                String bpath = (i + 1 < args.length && !args[i + 1].startsWith("-")) ? args[i + 1] : null;
                System.exit(runBench(bpath));
            } else if (arg.equals("--magma")) {
                modeMagma = true;
            } else if (arg.equals("--from-java")) {
                modeFromJava = true;
            } else if (arg.equals("--check")) {
                modeCheck = true;
            } else if (arg.equals("--compile")) {
                modeCompile = true;
            } else if (arg.equals("--run")) {
                modeRun = true;
            } else if (arg.equals("-o") && i + 1 < args.length) {
                outputBin = args[++i];
            } else if (arg.equals("--indent") && i + 1 < args.length) {
                String val = args[++i];
                if (val.equals("tab") || val.equals("\\t")) {
                    indentOpt = "\t";
                } else {
                    try {
                        int n = Integer.parseInt(val);
                        if (n <= 0 || n > 63) throw new NumberFormatException();
                        indentOpt = " ".repeat(n);
                    } catch (NumberFormatException e) {
                        System.err.println("magma error: --indent must be 1..63 or 'tab'");
                        System.exit(1);
                    }
                }
            } else if (arg.equals("--help") || arg.equals("-h")) {
                printUsage();
                System.exit(0);
            } else if (!arg.startsWith("-")) {
                inputPath = arg;
            } else {
                System.err.println("magma error: unknown option '" + arg + "'");
                System.exit(1);
            }
        }

        if (inputPath == null) {
            System.err.println("magma error: missing input file");
            System.exit(1);
        }

        String src;
        try {
            src = Files.readString(Path.of(inputPath), StandardCharsets.UTF_8);
        } catch (IOException e) {
            System.err.println("magma error: cannot read '" + inputPath + "'");
            System.exit(1);
            return;
        }

        try {
            if (modeFromJava) {
                System.out.print(magmaFromJavaIndent(src, indentOpt));
                return;
            }
            if (modeMagma) {
                System.out.print(magmaFormatIndent(src, indentOpt));
                return;
            }

            String javaCode = magmaToJava(src);
            if (modeCheck) {
                return;
            }
            if (modeCompile || modeRun) {
                System.exit(compileOrRunJava(javaCode, outputBin, modeRun));
            }
            System.out.print(javaCode);
        } catch (MagmaException e) {
            System.err.printf("magma error:%d:%d: %s%n", e.line, e.col, e.getMessage());
            System.exit(1);
        }
    }
}
