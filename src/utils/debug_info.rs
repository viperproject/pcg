use std::{backtrace::Backtrace, sync::Mutex};

#[derive(Clone, Copy, Debug)]
pub struct DebugInfo<'a>(Option<&'a Mutex<DebugInfoData>>);

impl PartialOrd for DebugInfo<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DebugInfo<'_> {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl PartialEq for DebugInfo<'_> {
    /// DebugInfo values are always be considered equal; this prevents
    /// breaking derived `PartialEq` implementations for types that contain
    /// DebugInfo values.
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for DebugInfo<'_> {}

// serde and hash no-ops
impl serde::Serialize for DebugInfo<'_> {
    fn serialize<S>(&self, ser: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        ser.serialize_unit()
    }
}
impl<'de> serde::Deserialize<'de> for DebugInfo<'_> {
    fn deserialize<D>(deser: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        deser.deserialize_unit(serde::de::IgnoredAny)?;
        Ok(DEBUGINFO_NONE)
    }
}
impl std::hash::Hash for DebugInfo<'_> {
    fn hash<H>(&self, _state: &mut H)
    where
        H: std::hash::Hasher,
    {
    }
}

pub const DEBUGINFO_NONE: DebugInfo = DebugInfo(None);

pub struct DebugInfoData {
    pub backtrace: Backtrace,
    pub debug_notes: Vec<String>,
}

impl std::fmt::Debug for DebugInfoData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DebugInfoData").field("debug_notes", &self.debug_notes).finish()
    }
}

impl DebugInfoData {
    fn new() -> DebugInfoData {
        let backtrace = Backtrace::capture();
        DebugInfoData {
            backtrace,
            debug_notes: Vec::new(),
        }
    }

    fn add_debug_note(&mut self, note: String) {
        self.debug_notes.push(note);
    }
}

impl std::fmt::Display for DebugInfoData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Debug Notes: {}", self.debug_notes.concat())?;
        write!(f, "Backtrace: {}", self.backtrace)
    }
}

impl<'arena> DebugInfo<'arena> {
    pub fn new_static() -> DebugInfo<'static> {
        let debug_info = DebugInfo::new(|mutex| {
            let mutex = Box::new(mutex);
            Box::leak(mutex)
        });
        debug_info
    }

    pub fn new(
        alloc: impl Fn(Mutex<DebugInfoData>) -> &'arena Mutex<DebugInfoData>,
    ) -> DebugInfo<'arena> {
        let debug_info_data = alloc(Mutex::new(DebugInfoData::new()));
        DebugInfo(Some(debug_info_data))
    }

    pub fn add_debug_note_never_call_this_function_directly(&self, note: String) {
        if let Some(mutex) = self.0 {
            let mut data = mutex.lock().unwrap();
            data.add_debug_note(note);
        }
    }
}

impl std::fmt::Display for DebugInfo<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Some(data) => write!(f, "{}", data.lock().unwrap()),
            None => write!(f, "This entity was not created with debug info."),
        }
    }
}

#[macro_export]
macro_rules! add_debug_note {
    ($debug_info:expr, $($arg:tt)*) => {{
        $debug_info.add_debug_note_never_call_this_function_directly(format!($($arg)*))
    }};
}
