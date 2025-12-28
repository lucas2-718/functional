use std::{cell::RefCell, fmt::Debug, hash::Hash, rc::Rc};

pub trait GlobalMap<T> {
    fn insert(&self, v: Rc<T>) -> Rc<T>;
    fn remove(&self, v: Rc<T>);
}



#[derive(Clone)]
pub struct Unique<Q: Hash + GlobalMap<T>,T: Hash> {
    data: Rc<T>,
    q: Q,
}

impl<Q: Hash + GlobalMap<T> + PartialEq,T: Hash + PartialEq> PartialOrd for Unique<Q,T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.get_ptr().partial_cmp(&other.get_ptr())
    }
}

impl<Q: Hash + GlobalMap<T> + PartialEq + Eq,T: Hash + PartialEq + Eq> Ord for Unique<Q,T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get_ptr().cmp(&other.get_ptr())
    }
}

impl<Q: Hash + GlobalMap<T>,T: Hash + Debug> Debug for Unique<Q,T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{:?}",self.data)
    }
}

impl<Q: Hash + GlobalMap<T> + PartialEq, T: Hash + PartialEq> PartialEq for Unique<Q,T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::as_ptr(&self.data).eq(&Rc::as_ptr(&other.data)) && self.q.eq(&other.q)
    }
}

impl<Q: Hash + GlobalMap<T> + PartialEq + Eq, T: Hash + PartialEq + Eq> Eq for Unique<Q,T> {}

impl<Q: Hash + GlobalMap<T>, T: Hash> Hash for Unique<Q,T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.q.hash(state);
        Rc::as_ptr(&self.data).hash(state);
    }
}

impl<Q: Hash + GlobalMap<T>, T: Hash> Unique<Q,T> {
    pub fn new(data: Rc<T>, q: Q) -> Self {
        let data = q.insert(data);
        Self {
            data, q
        }
    }
    pub fn get_ptr(&self) -> *const T {
        Rc::as_ptr(&self.data)
    }
    pub fn get_ref(&self) -> &T {
        &*self.data
    }
}

impl<Q: Hash + GlobalMap<T>, T: Hash + Clone> Unique<Q,T> {
    pub fn clone_inner(&self) -> T {
        (*self.data).clone()
    }
}

impl<Q: Hash + GlobalMap<T>, T: Hash> Drop for Unique<Q,T> {
    fn drop(&mut self) {
        if Rc::strong_count(&self.data)<=2 {
            self.q.remove(self.data.clone())
        }
    }
}

#[derive(Clone,Debug)]
pub struct Cache<T>(RefCell<T>);

impl<T> PartialEq for Cache<T> {
    fn eq(&self, other: &Self) -> bool {
        true
    }
}

impl<T> Eq for Cache<T> {}

impl<T> Hash for Cache<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        
    }
}