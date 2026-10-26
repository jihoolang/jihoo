# Data by index

A jihoo struct cannot hold a reference ([borrowing](borrowing.md)), so a
graph, a tree with parent links or a cache refers to its parts by index.
The compiler is written this way: types, functions and locals are numbers
into tables. `std.arena` makes this style safe and short:

| type | for |
|------|-----|
| `Arena(T)` and `Id(T)` | values that are added and kept: nodes of a graph, syntax trees, interned names |
| `Pool(T)` and `Handle(T)` | values that are added and removed: entities, connections, timers |
| `Soa(T)` | many plain structs whose fields are processed one at a time |

## Arenas and ids

```jihoo
import std.arena

struct Node {
    name: String
    edges: Vec(arena.Id(Node))
}

var g = arena.Arena(Node).new()
let a = g.add(Node { name: "a".to_string(), edges: Vec(arena.Id(Node)).new() })
let b = g.add(Node { name: "b".to_string(), edges: Vec(arena.Id(Node)).new() })
g[a].edges.push(b)
g[b].edges.push(a)          // a cycle, which references could not make
println(g[g[a].edges[0]].name)
```

An `Id(T)` is 4 bytes and plain: it copies, compares, orders, hashes (so
it can be a `Map` key) and prints as `#3`. It carries its type, so an
`Id(Node)` cannot index an `Arena(Edge)`. That is a compile error, where a
bare `i64` would let it through. An arena never removes values, so an id
stays valid in the arena that made it. `ids()` iterates over every id in
order, `as_slice()` gives the values, and `Id(T).from_index(i)` and
`to_index()` convert to and from positions.

## Pools and handles

A `Pool(T)` also removes values and reuses their slots. A `Handle(T)` holds
a slot and the slot's generation, which changes on every insert and
remove. A handle to a removed value therefore never finds the value that
reuses its slot:

```jihoo
var p = arena.Pool(String).new()
let h1 = p.insert("one".to_string())
p.remove(h1)                         // Some("one")
let h2 = p.insert("two".to_string()) // the same slot, a new generation
p.contains(h1)                       // false
p.get(h1)                            // None
p[h1]                                // stops the program: a handle used after its value was removed
```

`get` and `get_mut` return `Option(ref T)` and `Option(inout T)`.
Indexing stops the program on a stale handle, as indexing past the end of
a `Vec` does. `handles()` lists the live ones.

## Struct of arrays

`Soa(T)` stores a vector of plain structs (or tuples) as one array per
field. A loop over one field then reads only that field's memory. It is
built from `T`'s fields with [reflection](reflection.md), so the
standard library needs no code per type:

```jihoo
struct Particle {
    x: f64
    y: f64
    alive: bool
}

var s = arena.Soa(Particle).new()
s.push(Particle { x: 1.0, y: 2.0, alive: true })
for x in s.column(field_index(Particle, "x")) {   // a [f64]
    ...
}
s.each_mut(field_index(Particle, "y"), fn(y) { y *= 2.0 })
let p = s.get(0)                                   // a Particle again
s.set(0, p)
```

`column(F)` is a slice of field `F` of every element, and its element type
is `field_type(T, F)`. Summing one field of a struct of eight `f64`s over
4 million elements, 50 times, takes 0.28 s with `Soa` and 0.74 s with a
`Vec` of structs, which reads all eight fields' memory.

`T` must be [`Plain`](generics.md#standard-traits), since the arrays copy
fields in and out. Its fields must also be visible to `std.arena`: public,
or in the program's main file. Reflection keeps privacy.

## With threads

Ids and handles are plain numbers, and arenas are ordinary values, so they
work with [`std.thread`](threads.md). For example,
`thread.map(ids.as_slice(), fn(id) { score(graph[id]) })` borrows the
arena while every thread reads it.
