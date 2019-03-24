use hashbrown::hash_map::{self, HashMap};
use parking_lot::{Mutex, MutexGuard};
use stable_deref_trait::StableDeref;

use std::borrow::Borrow;
use std::hash::{BuildHasher, Hash};
use std::mem;

pub struct CacheMap<K, V, S = hash_map::DefaultHashBuilder> {
    map: Mutex<HashMap<K, V, S>>,
}

impl<K, V> CacheMap<K, V, hash_map::DefaultHashBuilder>
where
    K: Hash + Eq,
{
    pub fn new() -> Self {
        Default::default()
    }
}

impl<K, V, S> CacheMap<K, V, S> {
    /// Entry point for `CacheMap`'s raw entry API.
    pub fn raw_entry<'a>(&'a self) -> RawEntryBuilder<'a, K, V, S> {
        RawEntryBuilder { map: &self.map }
    }
}

impl<K, V, S> CacheMap<K, V, S>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    pub fn contains<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.raw_entry().from_key(key) {
            RawEntry::Occupied(_) => true,
            RawEntry::Vacant(_) => false,
        }
    }

    /// Get the value stored for a given key, if it exists in the map.
    pub fn get<'a, Q: ?Sized>(&'a self, key: &Q) -> Option<&'a V::Target>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
        V: StableDeref,
    {
        match self.raw_entry().from_key(key) {
            RawEntry::Occupied(entry) => Some(entry.get()),
            _ => None,
        }
    }

    pub fn get_key_value<'a, Q: ?Sized>(&'a self, key: &Q) -> Option<(&'a K::Target, &'a V::Target)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
        K: StableDeref,
        V: StableDeref,
    {
        match self.raw_entry().from_key(key) {
            RawEntry::Occupied(entry) => Some((entry.key(), entry.get())),
            _ => None,
        }
    }

    /// Attempt to insert the given key/value pair into the map. Returns `true`
    /// if the new entry was successfully added, and `false` if the value already
    /// exists in the map.
    pub fn insert<'a>(&'a self, key: K, value: V) -> bool {
        self.insert_with(key, || value)
    }

    /// Attempt to insert the given key/value pair into the map. Returns `true`
    /// if the new entry was successfully added, and `false` if the value already
    /// exists in the map.
    ///
    /// The passed-in thunk is only evaluated if the key doesn't already exist in
    /// the map.
    pub fn insert_with<'a, F>(&'a self, key: K, thunk: F) -> bool
    where
        F: FnOnce() -> V,
    {
        match self.raw_entry().from_key(&key) {
            RawEntry::Occupied(_) => false,
            RawEntry::Vacant(entry) => {
                entry.insert(key, thunk());
                true
            }
        }
    }

    /// Attempt to insert the given key/value pair into the map. Returns `Ok(ref)`
    /// if the new entry was successfully added, and `Err(ref)` if an entry
    /// already exists.
    pub fn insert_ref<'a>(&'a self, key: K, value: V) -> Result<&'a V::Target, &'a V::Target>
    where
        V: StableDeref,
    {
        self.insert_ref_with(key, || value)
    }

    /// Attempt to insert the given key/value pair into the map. Returns `Ok(ref)`
    /// if the new entry was successfully added, and `Err(ref)` if an entry
    /// already exists.
    pub fn insert_ref_with<'a, F>(
        &'a self,
        key: K,
        thunk: F,
    ) -> Result<&'a V::Target, &'a V::Target>
    where
        F: FnOnce() -> V,
        V: StableDeref,
    {
        match self.raw_entry().from_key(&key) {
            RawEntry::Occupied(entry) => Err(entry.get()),
            RawEntry::Vacant(entry) => Ok(entry.insert(key, thunk()).get()),
        }
    }
}

impl<K, V, S> Default for CacheMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    fn default() -> Self {
        CacheMap {
            map: Default::default(),
        }
    }
}

/// A builder for computing where in a hash map a key-value pair would be stored.
pub struct RawEntryBuilder<'a, K, V, S> {
    map: &'a Mutex<HashMap<K, V, S>>,
}

impl<'a, K, V, S> RawEntryBuilder<'a, K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Look up a `RawEntry` for a given key. This takes a lock on the
    /// `CacheMap`'s internal data structure.
    pub fn from_key<Q: ?Sized>(self, k: &Q) -> RawEntry<'a, K, V, S>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.bind(|re| re.from_key(k))
    }

    /// Like `from_key`, but with a precomputed hash.
    pub fn from_key_hashed_nocheck<Q: ?Sized>(self, hash: u64, k: &Q) -> RawEntry<'a, K, V, S>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        self.bind(|re| re.from_key_hashed_nocheck(hash, k))
    }

    /// Like `from_key`, but with a custom matcher strategy.
    pub fn from_hash<F>(self, hash: u64, is_match: F) -> RawEntry<'a, K, V, S>
    where
        for<'b> F: FnMut(&'b K) -> bool,
    {
        self.bind(|re| re.from_hash(hash, is_match))
    }

    fn bind<F>(self, callback: F) -> RawEntry<'a, K, V, S>
    where
        for<'b> F:
            FnOnce(hash_map::RawEntryBuilderMut<'b, K, V, S>) -> hash_map::RawEntryMut<'b, K, V, S>,
    {
        let mut guard = self.map.lock();
        let base_entry = callback(guard.raw_entry_mut());

        // Clear out the lifetime information for `base_entry` so we can put it
        // in the same struct as `guard`.
        let entry = unsafe {
            mem::transmute::<
                hash_map::RawEntryMut<'_, K, V, S>,
                hash_map::RawEntryMut<'a, K, V, S>,
            >(base_entry)
        };

        match entry {
            hash_map::RawEntryMut::Occupied(entry) => {
                let (key, value) = entry.into_key_value();
                RawEntry::Occupied(RawOccupiedEntry {
                    _guard: guard,
                    unsafe_key: key,
                    unsafe_value: value,
                })
            }
            hash_map::RawEntryMut::Vacant(entry) => RawEntry::Vacant(RawVacantEntry {
                _guard: guard,
                entry: entry,
            }),
        }
    }
}

/// A raw entry produced using the `raw_entry` API on `CacheMap`.
///
/// ## Locking
///
/// This object holds a lock on the target `CacheMap`'s internal data structure,
/// meaning that the `CacheMap` will be unavailable for reading or writing while
/// this object is alive.
pub enum RawEntry<'a, K, V, S> {
    Occupied(RawOccupiedEntry<'a, K, V, S>),
    Vacant(RawVacantEntry<'a, K, V, S>),
}

impl<'a, K, V, S> RawEntry<'a, K, V, S> {
    /// If this entry doesn't exist in the map yet, insert it with the given
    /// key/value. Returns a known-occupied entry.
    pub fn or_insert(self, default_key: K, default_value: V) -> RawOccupiedEntry<'a, K, V, S>
    where
        K: Hash,
        S: BuildHasher,
    {
        match self {
            RawEntry::Occupied(entry) => entry,
            RawEntry::Vacant(entry) => entry.insert(default_key, default_value),
        }
    }

    /// If this entry doesn't exist in the map yet, call `default`, and insert it
    /// with the returned key/value. Returns a known-occupied entry.
    pub fn or_insert_with<F>(self, default: F) -> RawOccupiedEntry<'a, K, V, S>
    where
        F: FnOnce() -> (K, V),
        K: Hash,
        S: BuildHasher,
    {
        match self {
            RawEntry::Occupied(entry) => entry,
            RawEntry::Vacant(entry) => {
                let (key, value) = default();
                entry.insert(key, value)
            }
        }
    }

    pub fn is_occupied(&self) -> bool {
        match self {
            RawEntry::Occupied(_) => true,
            RawEntry::Vacant(_) => false,
        }
    }
}

/// A `CacheMap` entry which is already filled.
///
/// ## Locking
///
/// This object holds a lock on the target `CacheMap`'s internal data structure,
/// meaning that the `CacheMap` will be unavailable for reading or writing while
/// this object is alive.
pub struct RawOccupiedEntry<'a, K, V, S> {
    _guard: MutexGuard<'a, HashMap<K, V, S>>,
    // WARNING: These lifetimes are lies, don't hand out references for the full
    // lifetime of &'a to anything but a StableDeref target.
    unsafe_key: &'a K,
    unsafe_value: &'a V,
}

impl<'a, K, V, S> RawOccupiedEntry<'a, K, V, S> {
    /// Borrow a reference to the raw key stored in the map.
    pub fn key_raw(&self) -> &K {
        // This is OK, as we bind the lifetime of the reference to `self`
        self.unsafe_key
    }

    /// Borrow a reference to the raw value stored in the map.
    pub fn get_raw(&self) -> &V {
        // This is OK, as we bind the lifetime of the reference to `self`
        self.unsafe_value
    }

    /// Get an extended reference to the value behind the key. This requires that
    /// `K` have a stable deref target (like `String` or `Box`).
    pub fn key(&self) -> &'a K::Target
    where
        K: StableDeref,
    {
        let raw = &**self.key_raw();
        unsafe { &*(raw as *const K::Target) }
    }

    /// Get an extended reference to the value behind the value. This requires
    /// that `V` have a stable deref target (like `String` or `Box`).
    pub fn get(&self) -> &'a V::Target
    where
        V: StableDeref,
    {
        let raw = &**self.get_raw();
        unsafe { &*(raw as *const V::Target) }
    }
}

/// A `CacheMap` entry which has yet to be filled.
///
/// ## Locking
///
/// This object holds a lock on the target `CacheMap`'s internal data structure,
/// meaning that the `CacheMap` will be unavailable for reading or writing while
/// this object is alive.
pub struct RawVacantEntry<'a, K, V, S> {
    _guard: MutexGuard<'a, HashMap<K, V, S>>,
    entry: hash_map::RawVacantEntryMut<'a, K, V, S>,
}

impl<'a, K, V, S> RawVacantEntry<'a, K, V, S> {
    /// Fill this vacant entry with the given key/value pair. Returns a now
    /// known-occupied entry.
    pub fn insert(self, key: K, value: V) -> RawOccupiedEntry<'a, K, V, S>
    where
        K: Hash,
        S: BuildHasher,
    {
        let (key, value) = self.entry.insert(key, value);
        RawOccupiedEntry {
            _guard: self._guard,
            unsafe_key: key,
            unsafe_value: value,
        }
    }

    /// Fill this vacant entry with a given key/value pair using a precomputed
    /// hash. Returns a now known-occupied entry.
    pub fn insert_hashed_nocheck(self, hash: u64, key: K, value: V) -> RawOccupiedEntry<'a, K, V, S>
    where
        K: Hash,
        S: BuildHasher,
    {
        let (key, value) = self.entry.insert_hashed_nocheck(hash, key, value);
        RawOccupiedEntry {
            _guard: self._guard,
            unsafe_key: key,
            unsafe_value: value,
        }
    }
}

#[test]
fn make() {
    let map = CacheMap::new();
    map.insert("Hello", "World");

    assert_eq!(map.get_key_value("Hello"), Some(("Hello", "World")));
}

/*
#[test]
fn unsafe_thing() {
    use std::cell::Cell;
    #[derive(Debug)]
    struct UnsafeThing<'a> {
        payload: u32,
        other: Cell<Option<&'a UnsafeThing<'a>>>,
    }

    impl<'a> Drop for UnsafeThing<'a> {
        fn drop(&mut self) {
            if let Some(other) = self.other.get() {
                println!("other.payload = {}", other.payload);
            } else {
                println!("other is None");
            }
        }
    }

    let map = CacheMap::new();
    let one = map.insert_ref(1, Box::new(UnsafeThing {
        payload: 1,
        other: Cell::new(None),
    })).unwrap();
    let two = map.insert_ref(2, Box::new(UnsafeThing {
        payload: 2,
        other: Cell::new(Some(one)),
    })).unwrap();
}
*/
