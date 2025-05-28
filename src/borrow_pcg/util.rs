#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct ExploreFrom<Current, Connect> {
    current: Current,
    connect: Connect,
}

impl<Current: Copy, Connect: Copy> ExploreFrom<Current, Connect> {
    pub(crate) fn new(current: Current, connect: Connect) -> Self {
        Self { current, connect }
    }

    pub(crate) fn connect(&self) -> Connect {
        self.connect
    }

    pub(crate) fn current(&self) -> Current {
        self.current
    }

    pub(crate) fn extend(&self, node: Current) -> Self {
        Self {
            current: node,
            connect: self.connect,
        }
    }
}

impl<Current: std::fmt::Display, Connect: Copy + std::fmt::Display> std::fmt::Display
    for ExploreFrom<Current, Connect>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Current: {}\nConnect: {}",
            self.current,
            self.connect
        )
    }
}
