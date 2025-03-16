use super::NodeId;

pub(super) struct IdLookup<T>(char, Vec<T>);

impl<T: Eq + Clone> IdLookup<T> {
    pub(super) fn new(prefix: char) -> Self {
        Self(prefix, vec![])
    }

    pub(super) fn existing_id(&mut self, item: &T) -> Option<NodeId> {
        self.1
            .iter()
            .position(|x| x == item)
            .map(|idx| NodeId(self.0, idx))
    }

    pub(super) fn node_id(&mut self, item: &T) -> NodeId {
        if let Some(idx) = self.existing_id(item) {
            idx
        } else {
            self.1.push(item.clone());
            NodeId(self.0, self.1.len() - 1)
        }
    }
}
