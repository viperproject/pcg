// Example usage of the semicolon-separated format for SelectedCrateTestCase
// Format: crate_name;version;date;function_name;num_bbs

fn main() {
    // Example format strings
    let examples = vec![
        // Format for entire crate testing (no function specified)
        "tracing-subscriber;0.3.19;2025-03-13;;",
        
        // Format for specific function with basic block count
        "syn;2.0.100;2025-03-13;punctuated::Pair::<T, P>::value_mut;6",
        
        // Format for specific function without basic block count
        "ahash;0.8.11;2025-03-13;random_state::RandomState::with_seed;",
        
        // Format without date (optional field)
        "some-crate;1.0.0;;some::function;10",
        
        // Complex function name with generics
        "regex-automata;0.4.9;2025-03-13;<util::captures::GroupInfoAllNames<'a> as core::iter::Iterator>::next;33",
    ];

    println!("Semicolon-separated format examples:\n");
    println!("Format: crate_name;version;date;function_name;num_bbs\n");
    
    for (i, example) in examples.iter().enumerate() {
        println!("Example {}:", i + 1);
        println!("  Raw: {}", example);
        
        let parts: Vec<&str> = example.split(';').collect();
        if parts.len() == 5 {
            println!("  Parsed:");
            println!("    Crate: {}", parts[0]);
            println!("    Version: {}", parts[1]);
            println!("    Date: {}", if parts[2].is_empty() { "(none)" } else { parts[2] });
            println!("    Function: {}", if parts[3].is_empty() { "(entire crate)" } else { parts[3] });
            println!("    Basic blocks: {}", if parts[4].is_empty() { "(not specified)" } else { parts[4] });
        }
        println!();
    }

    // Example of generating format strings from data
    println!("Generating format strings:\n");
    
    let test_cases = vec![
        ("my-crate", "1.0.0", Some("2025-03-13"), Some("my::function"), Some(15)),
        ("another-crate", "2.0.0", None, None, None),
        ("third-crate", "0.5.0", Some("2025-01-01"), Some("complex::func<T>"), None),
    ];
    
    for (crate_name, version, date, function, num_bbs) in test_cases {
        let formatted = format!(
            "{};{};{};{};{}",
            crate_name,
            version,
            date.unwrap_or(""),
            function.unwrap_or(""),
            num_bbs.map(|n| n.to_string()).unwrap_or_default()
        );
        println!("  {}", formatted);
    }
}