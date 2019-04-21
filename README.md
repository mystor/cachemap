# CacheMap

An append-only threadsafe hash map, with arena-like allocation behaviour. All
operations on `CacheMap` may be performed with non-`mut` references.

If the key or value is `StableDeref`, methods will return a shared reference
to their target which may live as long as the `CacheMap` itself.