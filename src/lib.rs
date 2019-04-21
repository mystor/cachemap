#![cfg_attr(feature = "raw_entry", feature(hash_raw_entry))]

use stable_deref_trait::StableDeref;

use std::borrow::Borrow;
use std::collections::hash_map::{self, HashMap};
use std::hash::{BuildHasher, Hash};
use std::sync::{Mutex, MutexGuard};

/// internal helper macro - performs a transmute cast to relax lifetime
/// parameters on an object with the given type.
///
/// Unsafe to use, as it violates borrow-checker guarantees.
macro_rules! unsafe_relax_lifetime {
    ($e:expr, $t:ty) => {
        {
            // Rustc doesn't understand that two generic types with mismatched
            // lifetime parameters are the same size, so `transmute_copy` has to
            // be used instead, followed by a `forget` to clean up the old
            // value.
            let e = $e;
            let e2 = unsafe { ::std::mem::transmute_copy::<$t, $t>(&e) };
            ::std::mem::forget(e);
            e2
        }
    };
}

pub struct CacheMap<K, V, S = hash_map::RandomState> {
    map: Mutex<HashMap<K, V, S>>,
}

impl<K, V> CacheMap<K, V, hash_map::RandomState>
where
    K: Hash + Eq,
{
    pub fn new() -> Self {
        Default::default()
    }
}

impl<K, V, S> CacheMap<K, V, S> {
    /// Entry point for `CacheMap`'s raw entry API.
    #[cfg(feature = "raw_entry")]
    pub fn raw_entry<'a>(&'a self) -> RawEntryBuilder<'a, K, V, S> {
        RawEntryBuilder { map: self }
    }

    /// Acquire the internal lock, ignoring poisoning.
    fn lock(&self) -> MutexGuard<HashMap<K, V, S>> {
        self.map.lock().unwrap_or_else(|pe| pe.into_inner())
    }
}

impl<K, V, S> CacheMap<K, V, S>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    /// Get the value stored for a given key, if it exists in the map.
    pub fn get<'a, Q: ?Sized>(&'a self, key: &Q) -> Option<&'a V::Target>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
        V: StableDeref,
    {
        self.lock()
            .get(key)
            .map(|rv| unsafe_relax_lifetime!(&**rv, &'_ V::Target))
    }

    /// Attempt to insert the given key/value pair into the map. Returns `true`
    /// if the new entry was successfully added, and `false` if the value already
    /// exists in the map.
    pub fn insert<'a>(&'a self, key: K, value: V) -> bool {
        self.lock().insert(key, value).is_none()
    }

    /// Entry point for the `entry` API on `cachemap`.
    ///
    /// An internal lock will be held while the `Entry` object is alive,
    /// preventing other reads or mutations.
    pub fn entry<'a>(&'a self, key: K) -> Entry<'a, K, V, S> {
        let mut guard = self.lock();

        // Relax the lifetime of the entry object such that it can be stored in
        // the same struct as the guard without violating the borrow-checker.
        match unsafe_relax_lifetime!(guard.entry(key), hash_map::Entry<'_, K, V>) {
            hash_map::Entry::Occupied(entry) => Entry::Occupied(OccupiedEntry {
                _guard: guard,
                entry: entry,
            }),
            hash_map::Entry::Vacant(entry) => Entry::Vacant(VacantEntry {
                _guard: guard,
                entry: entry,
            }),
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

pub enum Entry<'a, K, V, S> {
    Occupied(OccupiedEntry<'a, K, V, S>),
    Vacant(VacantEntry<'a, K, V, S>),
}

impl<'a, K, V, S> Entry<'a, K, V, S> {
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(e) => e.key(),
            Entry::Vacant(e) => e.key(),
        }
    }
}

impl<'a, K, V, S> Entry<'a, K, V, S>
where
    V: StableDeref,
{
    pub fn or_insert(self, default: V) -> &'a V::Target {
        self.or_insert_with(|| default)
    }

    pub fn or_insert_with<F>(self, default: F) -> &'a V::Target
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(e) => e.get_ref(),
            Entry::Vacant(e) => e.insert(default()),
        }
    }
}

pub struct OccupiedEntry<'a, K, V, S> {
    _guard: MutexGuard<'a, HashMap<K, V, S>>,
    entry: hash_map::OccupiedEntry<'a, K, V>,
}

impl<'a, K, V, S> OccupiedEntry<'a, K, V, S> {
    pub fn key(&self) -> &K {
        self.entry.key()
    }

    pub fn get(&self) -> &V {
        self.entry.get()
    }

    pub fn key_ref(&self) -> &'a K::Target
    where
        K: StableDeref,
    {
        unsafe_relax_lifetime!(&**self.key(), &'_ K::Target)
    }

    pub fn get_ref(&self) -> &'a V::Target
    where
        V: StableDeref,
    {
        unsafe_relax_lifetime!(&**self.get(), &'_ V::Target)
    }
}

pub struct VacantEntry<'a, K, V, S> {
    _guard: MutexGuard<'a, HashMap<K, V, S>>,
    entry: hash_map::VacantEntry<'a, K, V>,
}

impl<'a, K, V, S> VacantEntry<'a, K, V, S> {
    pub fn key(&self) -> &K {
        self.entry.key()
    }

    pub fn into_key(self) -> K {
        self.entry.into_key()
    }

    pub fn insert_raw(self, value: V) {
        self.entry.insert(value);
    }

    pub fn insert(self, value: V) -> &'a V::Target
    where
        V: StableDeref,
    {
        let tgt = &*value as *const V::Target;
        self.insert_raw(value);
        unsafe { &*tgt }
    }

    pub fn insert_key_value(self, value: V) -> (&'a K::Target, &'a V::Target)
    where
        K: StableDeref,
        V: StableDeref,
    {
        let key = &**self.key() as *const K::Target;
        let tgt = &*value as *const V::Target;
        self.insert_raw(value);
        unsafe { (&*key, &*tgt) }
    }
}

/// A builder for computing where in a hash map a key-value pair would be stored.
#[cfg(feature = "raw_entry")]
pub struct RawEntryBuilder<'a, K, V, S> {
    map: &'a CacheMap<K, V, S>,
}

#[cfg(feature = "raw_entry")]
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
        let entry = unsafe_relax_lifetime!(base_entry, hash_map::RawEntryMut<'_, K, V, S>);
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
#[cfg(feature = "raw_entry")]
pub enum RawEntry<'a, K, V, S> {
    Occupied(RawOccupiedEntry<'a, K, V, S>),
    Vacant(RawVacantEntry<'a, K, V, S>),
}

#[cfg(feature = "raw_entry")]
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
#[cfg(feature = "raw_entry")]
pub struct RawOccupiedEntry<'a, K, V, S> {
    _guard: MutexGuard<'a, HashMap<K, V, S>>,
    // WARNING: These lifetimes are lies, don't hand out references for the full
    // lifetime of &'a to anything but a StableDeref target.
    unsafe_key: &'a K,
    unsafe_value: &'a V,
}

#[cfg(feature = "raw_entry")]
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
#[cfg(feature = "raw_entry")]
pub struct RawVacantEntry<'a, K, V, S> {
    _guard: MutexGuard<'a, HashMap<K, V, S>>,
    entry: hash_map::RawVacantEntryMut<'a, K, V, S>,
}

#[cfg(feature = "raw_entry")]
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

    // assert_eq!(map.get_key_value("Hello"), Some(("Hello", "World")));
}

#[test]
fn loopy() {
    use std::cell::Cell;
    #[derive(Debug)]
    struct LoopyThing<'a> {
        payload: u32,
        other: Cell<Option<&'a LoopyThing<'a>>>,
    }

    let map = CacheMap::new();
    let one = map.entry(1).or_insert(Box::new(LoopyThing {
        payload: 1,
        other: Cell::new(None),
    }));
    let two = map.entry(2).or_insert(Box::new(LoopyThing {
        payload: 2,
        other: Cell::new(Some(one)),
    }));
    one.other.set(Some(two))
}
