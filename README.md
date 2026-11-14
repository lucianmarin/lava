# Magma Language Specification

**Magma** (`.magma`) is a **1-to-1 Pythonic syntax skin for Java**.

Unlike Kotlin, Groovy, or Scala—which introduce their own compilers, standard libraries, runtime dependencies, or complex type systems—Magma has **zero runtime overhead and zero external dependencies**:
- Every line of Magma maps deterministically **1-to-1** to standard Java (and back).
- Block structure is defined by **Python-style indentation** and a trailing colon (`:`), eliminating curly braces `{}` and semicolons `;`.
- Function, method, parameter, variable, and field declarations use **Pythonic `def` and `name: type` annotations**, with `-> ret_type` for return types.
- Generics use Python-style square brackets (`list[i32]`, `dict[str, f64]`, `Optional[User]`) with automatic primitive-to-boxed mapping (`i32` → `int` in value position, `Integer` inside `<...>`).
- Supports **list, set, and dict comprehensions** for both fixed-size Java arrays and Java Collections (`ArrayList`, `TreeSet`, `TreeMap`).
- Uses Java's exact object model, primitives, arrays, standard library, and `javac` compiler unchanged.

---

## 1. How Magma Compares to Java, Kotlin, Groovy, and Scala

| Feature | Java | Kotlin | Groovy | Scala 3 | **Magma (`.magma`)** |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Block delimiters** | `{ ... }` | `{ ... }` | `{ ... }` | Indentation | **Indentation (`:`)** |
| **Statement terminators** | `;` required | Optional | Optional | Optional | **Newline (no `;`)** |
| **Method keyword** | None | `fun` | `def` | `def` | **`def`** |
| **Type position** | Prefix (`int x`) | Postfix (`x: Int`) | Prefix / dynamic | Postfix (`x: Int`) | **Postfix (`x: i32`)** |
| **Generics syntax** | `List<Integer>` | `List<Int>` | `List<Integer>` | `List[Int]` | **`list[i32]`** |
| **Comprehensions** | None (Streams) | `.map` / `.filter` | `.collect` | `for ... yield` | **`[x for x in a if c]`** |
| **Runtime / Stdlib** | JDK only | `kotlin-stdlib` | `groovy.jar` (MOP) | `scala3-library` | **JDK only (0 deps)** |
| **1:1 Java bijection** | — | No | No | No | **Yes (`--from-java`)** |

---

## 2. Side-by-Side Comparison: Java vs. Magma

### Standard Java (`.java`)
```java
import java.util.ArrayList;

public class Shapes {
    public static final double PI = 3.141592653589793;

    static class Circle {
        double radius;
        String label;

        Circle(double r, String name) {
            this.radius = r;
            this.label = name;
        }
    }

    static double circle_area(Circle c) {
        if (c == null || c.radius <= 0.0) {
            return 0.0;
        }
        return PI * c.radius * c.radius;
    }

    public static void main(String[] args) {
        double[] radii = {1.0, 2.5, 5.0};
        String[] names = {"unit", "medium", "large"};

        for (int i = 0; i < 3; i++) {
            Circle c = new Circle(radii[i], names[i]);
            Object raw = c;
            double area = circle_area((Circle)raw);
            if (area > 10.0 && !(i == 0)) {
                System.out.printf("[%s] r=%.1f -> area=%.2f (large)\n", c.label, c.radius, area);
            } else if (area > 0.0) {
                System.out.printf("[%s] r=%.1f -> area=%.2f (small)\n", c.label, c.radius, area);
            } else {
                System.out.printf("invalid circle\n");
            }
        }
    }
}
```

### Magma (`.magma`)
```python
# Geometry & Shapes in Magma (4-space indentation)

public class Shapes:
    PI = 3.141592653589793

    static class Circle:
        radius: f64
        label: str

        def Circle(r: f64, name: str):
            self.radius = r
            self.label = name

    static def circle_area(c: Circle) -> f64:
        if c == nil or c.radius <= 0.0:
            return 0.0
        return PI * c.radius * c.radius

    public static def main(args: str[]):
        radii: f64[3] = {1.0, 2.5, 5.0}
        names: str[3] = {"unit", "medium", "large"}

        for i in range(3):
            c: Circle = new Circle(radii[i], names[i])
            raw: any = c
            area: f64 = circle_area(cast(Circle, raw))
            if area > 10.0 and not (i == 0):
                printf("[%s] r=%.1f -> area=%.2f (large)\n", c.label, c.radius, area)
            elif area > 0.0:
                printf("[%s] r=%.1f -> area=%.2f (small)\n", c.label, c.radius, area)
            else:
                printf("invalid circle\n")
```

---

## 3. Complete Syntax Specification

### 3.1 Indentation & Whitespace Rules
1. **Flexible Indentation**: A file may use **any consistent number of spaces** (e.g., 2, 4, or 8 spaces) **or tabs (`\t`)** for indentation.
2. **Auto-Detection**: The indentation character and width `W` are automatically detected from the **first indented line** in the file.
3. **Strict Consistency**:
   - Every indented line in the file must use the same indentation character as the first indented line, and its leading count must be an exact multiple `k * W`.
   - Mixing spaces and tabs on the same line or across lines in the same file is a syntax error.
   - Trailing whitespace at the end of a line and UTF-8 BOMs are syntax errors.
4. **Universal Newlines**: `\n` (LF), `\r\n` (CRLF), and `\r` (CR) are all accepted.
5. **Blocks**:
   - A line ending with `:` opens a block (`{` in Java) and requires the next non-blank, non-comment line to be indented by `level + 1`.
   - Dedenting by `d` levels automatically emits `d` closing braces `}`.
   - Empty blocks use `pass`.

### 3.2 Comments, Packages, Imports & Constants

| Magma Syntax | Transpiled Java Syntax | Notes |
| :--- | :--- | :--- |
| `# full-line or inline comment` | `// full-line or inline comment` | Outside string/char literals |
| `package com.example.app` | `package com.example.app;` | Package declaration |
| `import java.util.ArrayList` | `import java.util.ArrayList;` | Standard import |
| `import ArrayList` | `import java.util.ArrayList;` | Shorthand for `java.util.*` classes |
| `from java.util import *` | `import java.util.*;` | Wildcard package import |
| `MAX_SIZE = 1024` | `public static final int MAX_SIZE = 1024;` | Untyped `ALL_CAPS = val` at class/root scope |
| `PI = 3.14159` | `public static final double PI = 3.14159;` | Inferred `int`, `long`, `double`, `boolean`, `char`, `String` |

### 3.3 Type Aliases, Arrays & `[T]` Generics

Magma provides concise primitive and collection type aliases that automatically map to Java primitives in value/array positions and to boxed types inside generic type arguments (`[T]` ↔ `<T>`):

| Magma Type | Java Primitive / Value Type | Java Boxed Generic Argument |
| :--- | :--- | :--- |
| `i8` | `byte` | `Byte` |
| `i16` | `short` | `Short` |
| `i32` | `int` | `Integer` |
| `i64` | `long` | `Long` |
| `f32` | `float` | `Float` |
| `f64` | `double` | `Double` |
| `bool` | `boolean` | `Boolean` |
| `char` | `char` | `Character` |
| `str` | `String` | `String` |
| `any` | `Object` | `Object` |
| `list[T]` | `ArrayList<T>` | `ArrayList<T>` |
| `set[T]` | `TreeSet<T>` | `TreeSet<T>` |
| `unordered_set[T]` | `HashSet<T>` | `HashSet<T>` |
| `dict[K, V]` | `TreeMap<K, V>` | `TreeMap<K, V>` |
| `unordered_map[K, V]` | `HashMap<K, V>` | `HashMap<K, V>` |
| `Type[T]` | `Type<T>` | Any Java generic type (`Optional[str]` ↔ `Optional<String>`) |

### 3.4 Declarations (Variables, Fields, Arrays, Methods, Classes, Records, Enums)

| Construct | Magma Syntax | Transpiled Java Syntax |
| :--- | :--- | :--- |
| **Variable / Field** | `x: i32 = 10` | `int x = 10;` |
| **Final (`const`)** | `const limit: i32 = 100` | `final int limit = 100;` |
| **Field with modifiers** | `private static count: i64 = 0` | `private static long count = 0;` |
| **Unsized array** | `args: str[]` | `String[] args;` |
| **Sized array alloc** | `grid: f64[4][4]` | `double[][] grid = new double[4][4];` |
| **Array initializer** | `vals: i32[3] = {1, 2, 3}` | `int[] vals = {1, 2, 3};` |
| **Generic constructor** | `items: list[i32] = new list[i32]()` | `ArrayList<Integer> items = new ArrayList<Integer>();` |
| **Method with return** | `static def add(a: i32, b: i32) -> i32:` | `static int add(int a, int b) {` |
| **Void method** | `def reset(self_id: i32):` | `void reset(int self_id) {` |
| **Constructor** | `def Circle(r: f64):` | `Circle(double r) {` |
| **Main entrypoint** | `public static def main(args: str[]):` or `def main():` | `public static void main(String[] args) {` |
| **Interface prototype** | `def compute(x: f64) -> f64` | `double compute(double x);` |
| **Class inheritance** | `class Dog(Animal):` | `class Dog extends Animal {` |
| **Record** | `record Vec2(x: f64, y: f64)` | `record Vec2(double x, double y) {}` |
| **Enum** | `enum Mode:` (entries on indented lines) | `enum Mode {` (auto-comma on entries) |

### 3.5 Control Flow & Loops

| Construct | Magma Syntax | Transpiled Java Syntax |
| :--- | :--- | :--- |
| **Conditional** | `if a and not b:` | `if (a && !b) {` |
| **Else-if** | `elif a or c:` | `} else if (a \|\| c) {` |
| **Else** | `else:` | `} else {` |
| **Range (0..stop)** | `for i in range(n):` | `for (int i = 0; i < n; i++) {` |
| **Range (start..stop)** | `for i in range(2, n):` | `for (int i = 2; i < n; i++) {` |
| **Range (with step)** | `for i in range(0, n, 2):` | `for (int i = 0; i < n; i += 2) {` |
| **Range (negative step)** | `for i in range(n, 0, -1):` | `for (int i = n; i > 0; i--) {` |
| **Enhanced for-in** | `for item in collection:` | `for (var item : collection) {` |
| **Typed for-in** | `for item: str in names:` | `for (String item : names) {` |
| **3-clause for** | `for i: i32 = 0; i < n; i++:` | `for (int i = 0; i < n; i++) {` |
| **While** | `while cond:` | `while (cond) {` |
| **Do-while** | `do:` ... `while cond` | `do {` ... `} while (cond);` |
| **Switch / Case** | `switch x:` / `case 1:` / `default:` | `switch (x) {` / `case 1:` / `default:` |
| **Try / Catch / Finally** | `try:` / `catch (e: Exception):` / `finally:` | `try {` / `} catch (Exception e) {` / `} finally {` |

### 3.6 List, Set, and Dict Comprehensions (Arrays & Java Collections)

Magma supports Pythonic **list (`[...]`), set (`{...}`), and dict (`{k: v ...}`) comprehensions** with an optional `if` filter for both **fixed-size Java arrays** (zero boxing overhead) and **Java Collections** (`ArrayList`, `TreeSet`, `TreeMap`):

| Comprehension Kind | Target Type | Magma Syntax | Transpiled Java Code |
| :--- | :--- | :--- | :--- |
| **Array List Comp** | `T[N]` | `sq: i32[8] = [i * i for i in range(8)]` | `int[] sq = new int[8];`<br>`for (int i = 0; i < 8; i++) { sq[i] = i * i; }` |
| **Array Set Comp** | `bool[N]` | `ev: bool[16] = {i for i in range(16) if i % 2 == 0}` | `boolean[] ev = new boolean[16];`<br>`for (int i = 0; i < 16; i++) { if (i % 2 == 0) { ev[i] = true; } }` |
| **Array Dict Comp** | `T[N]` | `tb: i32[8] = {i: i * 10 for i in range(8) if i > 0}` | `int[] tb = new int[8];`<br>`for (int i = 0; i < 8; i++) { if (i > 0) { tb[i] = i * 10; } }` |
| **Java `ArrayList`** | `list[T]` | `v: list[i32] = [x * 2 for x in sq if x > 0]` | `ArrayList<Integer> v = new ArrayList<>();`<br>`for (var x : sq) { if (x > 0) { v.add(x * 2); } }` |
| **Java `TreeSet`** | `set[T]` | `s: set[i32] = {x for x in v}` | `TreeSet<Integer> s = new TreeSet<>();`<br>`for (var x : v) { s.add(x); }` |
| **Java `TreeMap`** | `dict[K, V]` | `m: dict[i32, i32] = {x: x + 1 for x in s if x < 100}` | `TreeMap<Integer, Integer> m = new TreeMap<>();`<br>`for (var x : s) { if (x < 100) { m.put(x, x + 1); } }` |

All 6 comprehension forms are **100% bijective**: `magma --from-java` recognizes the generated Java initialization loops and folds them back into single-line Magma comprehensions.

### 3.7 Expressions, Operators, Casts & Console Built-ins

| Magma Token / Call | Java Equivalent | Purpose |
| :--- | :--- | :--- |
| `and` | `&&` | Logical AND |
| `or` | `\|\|` | Logical OR |
| `not x` | `!x` | Logical NOT |
| `nil` / `None` | `null` | Null reference literal |
| `True` / `False` | `true` / `false` | Boolean literals (`true`/`false` also accepted) |
| `self` | `this` | Current object instance reference |
| `i32(x)`, `f64(x)`, `i64(x)` | `(int)x`, `(double)x`, `(long)x` | Scalar value conversion (`i8`, `i16`, `i32`, `i64`, `f32`, `f64`, `char`) |
| `cast(Type, expr)` | `(Type)expr` | Reference / object type cast |
| `isinstance(x, Type)` | `x instanceof Type` | Runtime type check |
| `printf(fmt, ...)` | `System.out.printf(fmt, ...)` | Formatted standard output |
| `println(x)` / `print(x)` | `System.out.println(x)` / `System.out.print(x)` | Standard output helpers |

---

## 4. Formal Grammar (EBNF)

```ebnf
module          = { line } ;
line            = [COMMENT] NEWLINE
                | INDENT_LEVEL statement [COMMENT] NEWLINE ;

statement       = package_stmt
                | import_stmt
                | const_assign
                | record_decl
                | block_stmt
                | var_decl
                | func_proto
                | simple_stmt ;

package_stmt    = "package" qualified_name ;
import_stmt     = "import" qualified_name
                | "from" qualified_name "import" ( IDENT | "*" ) ;
const_assign    = ALL_CAPS_IDENT "=" expr ;
record_decl     = [modifiers] "record" IDENT "(" [param_list] ")" ;

block_stmt      = block_header ":" NEWLINE INDENT { line } DEDENT ;
block_header    = [modifiers] ("def" | "fn") IDENT "(" [param_list] ")" ["->" type_spec] ["throws" type_list]
                | [modifiers] ("class" | "interface" | "enum" | "struct") IDENT ["(" type_spec ")"]
                | "if" expr
                | "elif" expr
                | "else"
                | "for" IDENT [":" type_spec] "in" "range" "(" expr ["," expr ["," expr]] ")"
                | "for" IDENT [":" type_spec] "in" expr
                | "for" (var_decl | expr) ";" expr ";" expr
                | "while" expr
                | "do"
                | "switch" expr
                | "case" expr
                | "default"
                | "try"
                | ("catch" | "except") "(" param ")"
                | "finally"
                | "synchronized" "(" expr ")" ;

func_proto      = [modifiers] ("def" | "fn") IDENT "(" [param_list] ")" ["->" type_spec] ;
param_list      = param { "," param } ;
param           = ["const" | "final"] IDENT ":" type_spec ;

var_decl        = [modifiers] IDENT ":" type_spec [ "=" (comprehension | expr) ] ;
comprehension   = "[" expr "for" for_clause [ "if" expr ] "]"
                | "{" expr "for" for_clause [ "if" expr ] "}"
                | "{" expr ":" expr "for" for_clause [ "if" expr ] "}" ;
type_spec       = IDENT [ "[" type_list "]" ] { "[" [expr] "]" } ;
simple_stmt     = "return" [expr] | "break" | "continue" | "pass" | expr ;
```

---

## 5. Building & CLI Usage

### Build from Source

Requires a standard JDK (`javac` and `java`, JDK 17+ recommended):

```sh
make          # Compiles Magma.java and packages the standalone ./magma executable
make test     # Runs the 18-case bidirectional conformance test suite
make bench    # Runs the transpilation throughput & code size benchmark
```

### CLI Commands

```sh
# 1. Transpile Magma (.magma) to standard Java (.java) on stdout
./magma examples/shapes.magma

# 2. Transpile, compile via javac, and run immediately
./magma --run examples/shapes.magma
./magma --run examples/comprehensions.magma
./magma --run examples/lmon.magma

# 3. Compile Magma (.magma) into a standalone executable binary
./magma --compile examples/shapes.magma -o shapes
./shapes

# 4. Convert existing Java (.java) source to Magma (4 spaces, 2 spaces, or tabs)
./magma --from-java SomeClass.java
./magma --from-java --indent 2 SomeClass.java
./magma --from-java --indent tab SomeClass.java

# 5. Canonicalize / re-indent a Magma file
./magma --magma --indent 4 examples/tabs.magma
```

---

## 6. Benchmark Results (250 Methods, 1,000 Iterations)

Measured on Apple Silicon (`aarch64`, OpenJDK 25) via `./magma --bench`:

| Metric | Result |
| :--- | :--- |
| **Java source size** | `107,675 bytes` (`105.2 KiB`) |
| **Magma 4-space size** | `93,906 bytes` (`91.7 KiB`, **`-12.8%` smaller than Java**) |
| **Magma tab (`\t`) size** | `72,879 bytes` (`71.2 KiB`, **`-32.3%` smaller than Java**) |
| **Magma (4-space) → Java** | **`472 files/s`** (`42.3 MiB/s`) |
| **Magma (tab) → Java** | **`502 files/s`** (`34.9 MiB/s`) |
| **Java → Magma (4-space)** | **`379 files/s`** (`38.9 MiB/s`) |
