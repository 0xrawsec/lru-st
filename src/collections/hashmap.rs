use crate::{Cursor, DoublyLinkedList};

use std::{
    collections::HashMap,
    fmt::Display,
    hash::Hash,
    //rc::{Rc, Weak},
    //sync::{Arc, Weak},
};

#[cfg(not(feature = "async"))]
use std::rc::{Rc, Weak};

#[cfg(feature = "async")]
use {std::sync::Arc as Rc, std::sync::Weak};

pub struct LruHashMap<K, V> {
    map: HashMap<Rc<K>, Cursor>,
    lru: DoublyLinkedList<(Weak<K>, V)>,
    capacity: usize,
}

impl<K, V> LruHashMap<K, V>
where
    K: Hash + Eq,
{
    pub fn with_capacity(capacity: usize) -> Self {
        LruHashMap {
            map: HashMap::new(),
            lru: DoublyLinkedList::with_capacity(capacity),
            capacity,
        }
    }

    #[inline]
    pub fn get(&mut self, k: &K) -> Option<&V> {
        if let Some((_k, v)) = self.map.get(k).and_then(|cursor| {
            self.lru.move_front(*cursor).unwrap();
            self.lru.front()
        }) {
            return Some(v);
        }
        None
    }

    #[inline]
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        if let Some((_k, v)) = self.map.get(k).and_then(|cursor| {
            self.lru.move_front(*cursor).unwrap();
            self.lru.front_mut()
        }) {
            return Some(v);
        }
        None
    }

    #[inline]
    pub fn contains_key(&mut self, k: &K) -> bool {
        self.get(k).is_some()
    }

    #[inline]
    pub fn insert(&mut self, k: K, v: V) {
        // we update value if already there
        if self.map.contains_key(&k) {
            let old = self.get_mut(&k).expect("value must exist");
            *old = v;
            return;
        }
        // if we arrive here the key/value needs to be inserted
        // if we reached capacity, we must delete the last used entry first
        if self.map.len() == self.capacity {
            if let Some((k, _v)) = self.lru.pop_back() {
                // we put this in a block so that we can debug_assert latter
                {
                    let key = k.upgrade().expect("weak reference must be valid");
                    self.map.remove(&key);
                }
                // Rc should have been dropped now because we have removed item from map
                debug_assert!(k.upgrade().is_none());
            };
        }
        let k = Rc::new(k);
        let cursor = self.lru.push_front((Rc::downgrade(&k), v));
        self.map.insert(k, cursor);
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl<K, V> Display for LruHashMap<K, V>
where
    K: Display,
    V: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        write!(f, "{{")?;
        for v in self.lru.iter() {
            let key = v.0.upgrade().expect("weak reference must be valid");
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}:{}", key, v.1)?;
            first = false;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_lru_hashmap() {
        let cap = 1000;
        let mut lru = LruHashMap::with_capacity(cap);
        for i in 0..cap * 2 {
            lru.insert(i, i)
        }
        assert_eq!(lru.len(), cap);
        assert_eq!(lru.get(&0), None);
        assert_eq!(lru.get(&cap), Some(&cap));
        lru.insert(cap + 42, 42);
        assert_eq!(lru.get(&(cap + 42)), Some(&42));
        println!("{}", lru);
    }
}
