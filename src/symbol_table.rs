// SPDX-FileCopyrightText: Copyright © 2025 hashcatHitman
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! # Symbol Table
//!
//! This module manages the symbol table for the Hack assembler, tracking and resolving
//! symbols to their respective addresses.

use std::collections::HashMap;

/// Represents the different types of symbols in Hack assembly
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolType {
    /// Predefined symbols in the Hack language (SP, LCL, etc.)
    Predefined,
    /// Labels defined in the code with (LABEL)
    Label,
    /// Variables referenced with @var but not predefined
    Variable,
}

/// Represents a symbol's address and type
#[derive(Debug, Clone)]
pub enum SymbolAddress {
    /// ROM address (for labels)
    Rom(u16),
    /// RAM address (for variables and predefined symbols)
    Ram(u16),
}

/// Symbol table for the Hack assembler
#[derive(Debug, Clone)]
pub struct SymbolTable {
    /// Maps symbol names to their address and type
    entries: HashMap<String, (SymbolAddress, SymbolType)>,
    /// Next available RAM address for variable allocation
    next_variable_address: u16,
}

impl SymbolTable {
    /// Creates a new symbol table with predefined symbols
    pub fn new() -> Self {
        let mut table = Self {
            entries: HashMap::new(),
            next_variable_address: 16, // Variables start at RAM[16]
        };

        // Add predefined symbols
        let predefined = vec![
            ("SP", 0), ("LCL", 1), ("ARG", 2), ("THIS", 3), ("THAT", 4),
            ("R0", 0), ("R1", 1), ("R2", 2), ("R3", 3), ("R4", 4),
            ("R5", 5), ("R6", 6), ("R7", 7), ("R8", 8), ("R9", 9),
            ("R10", 10), ("R11", 11), ("R12", 12), ("R13", 13), ("R14", 14), ("R15", 15),
            ("SCREEN", 16384), ("KBD", 24576)
        ];

        for (name, address) in predefined {
            table.entries.insert(
                name.to_string(),
                (SymbolAddress::Ram(address), SymbolType::Predefined)
            );
        }

        table
    }

    /// Adds a label symbol
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the label (without parentheses)
    /// * `address` - The ROM address where the label is defined
    ///
    /// # Returns
    ///
    /// * `Ok(())` if the label was added successfully
    /// * `Err(SymbolError::DuplicateLabel)` if a label with the same name already exists
    ///
    /// # Examples
    ///
    /// ```
    /// use hack_assembler::symbol_table::{SymbolTable, SymbolError};
    ///
    /// let mut table = SymbolTable::new();
    /// table.add_label("LOOP", 10)?;
    /// ```
    pub fn add_label(&mut self, name: &str, address: u16) -> Result<(), SymbolError> {
        // Check if symbol already exists as a label
        if let Some((_, symbol_type)) = self.entries.get(name) {
            if *symbol_type == SymbolType::Label {
                return Err(SymbolError::DuplicateLabel(name.to_string()));
            }
        }

        self.entries.insert(
            name.to_string(),
            (SymbolAddress::Rom(address), SymbolType::Label)
        );
        Ok(())
    }

    /// Gets or adds a variable symbol
    ///
    /// If the symbol exists (as any type), returns its address.
    /// If the symbol doesn't exist, adds it as a variable with the next available RAM address.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the variable
    ///
    /// # Returns
    ///
    /// The address associated with the symbol
    ///
    /// # Examples
    ///
    /// ```
    /// use hack_assembler::symbol_table::SymbolTable;
    ///
    /// let mut table = SymbolTable::new();
    /// let address = table.get_or_add_variable("counter");
    /// assert_eq!(address, 16); // First variable gets address 16
    /// ```
    pub fn get_or_add_variable(&mut self, name: &str) -> u16 {
        // If symbol already exists, return its address
        if let Some((address, _)) = self.entries.get(name) {
            match address {
                SymbolAddress::Ram(addr) => return *addr,
                SymbolAddress::Rom(addr) => return *addr,
            }
        }

        // Otherwise, allocate a new address for the variable
        let address = self.next_variable_address;
        self.next_variable_address += 1;

        self.entries.insert(
            name.to_string(),
            (SymbolAddress::Ram(address), SymbolType::Variable)
        );

        address
    }

    /// Gets the address for a symbol if it exists
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the symbol to look up
    ///
    /// # Returns
    ///
    /// * `Some(address)` if the symbol exists
    /// * `None` if the symbol doesn't exist
    ///
    /// # Examples
    ///
    /// ```
    /// use hack_assembler::symbol_table::SymbolTable;
    ///
    /// let table = SymbolTable::new();
    /// assert_eq!(table.get_address("SP"), Some(0));
    /// assert_eq!(table.get_address("UNKNOWN"), None);
    /// ```
    pub fn get_address(&self, name: &str) -> Option<u16> {
        self.entries.get(name).map(|(address, _)| {
            match address {
                SymbolAddress::Ram(addr) => *addr,
                SymbolAddress::Rom(addr) => *addr,
            }
        })
    }

    /// Gets the type of symbol if it exists
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the symbol to look up
    ///
    /// # Returns
    ///
    /// * `Some(&SymbolType)` if the symbol exists
    /// * `None` if the symbol doesn't exist
    ///
    /// # Examples
    ///
    /// ```
    /// use hack_assembler::symbol_table::{SymbolTable, SymbolType};
    ///
    /// let table = SymbolTable::new();
    /// assert_eq!(table.get_type("SP"), Some(&SymbolType::Predefined));
    /// assert_eq!(table.get_type("UNKNOWN"), None);
    /// ```
    pub fn get_type(&self, name: &str) -> Option<&SymbolType> {
        self.entries.get(name).map(|(_, symbol_type)| symbol_type)
    }

    /// Returns whether a symbol exists in the table
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the symbol to check
    ///
    /// # Returns
    ///
    /// * `true` if the symbol exists
    /// * `false` if the symbol doesn't exist
    ///
    /// # Examples
    ///
    /// ```
    /// use hack_assembler::symbol_table::SymbolTable;
    ///
    /// let table = SymbolTable::new();
    /// assert!(table.contains("SP"));
    /// assert!(!table.contains("UNKNOWN"));
    /// ```
    pub fn contains(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    /// Returns the number of symbols in the table
    ///
    /// # Returns
    ///
    /// The number of symbols in the table
    ///
    /// # Examples
    ///
    /// ```
    /// use hack_assembler::symbol_table::SymbolTable;
    ///
    /// let table = SymbolTable::new();
    /// assert!(table.len() > 0); // Table has predefined symbols
    /// ```
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns whether the table is empty
    ///
    /// # Returns
    ///
    /// * `true` if the table is empty
    /// * `false` if the table has at least one symbol
    ///
    /// # Examples
    ///
    /// ```
    /// use hack_assembler::symbol_table::SymbolTable;
    ///
    /// let table = SymbolTable::new();
    /// assert!(!table.is_empty()); // Table has predefined symbols
    /// ```
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Returns an iterator over all symbols and their addresses
    ///
    /// # Returns
    ///
    /// An iterator over (symbol_name, address) pairs
    ///
    /// # Examples
    ///
    /// ```
    /// use hack_assembler::symbol_table::SymbolTable;
    ///
    /// let table = SymbolTable::new();
    /// for (name, address) in table.iter() {
    ///     println!("{} -> {}", name, address);
    /// }
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (&String, u16)> + '_ {
        self.entries.iter().map(|(name, (address, _))| {
            let addr = match address {
                SymbolAddress::Ram(addr) => *addr,
                SymbolAddress::Rom(addr) => *addr,
            };
            (name, addr)
        })
    }

    /// Returns an iterator over symbols of a specific type
    ///
    /// # Arguments
    ///
    /// * `symbol_type` - The type of symbols to iterate over
    ///
    /// # Returns
    ///
    /// An iterator over (symbol_name, address) pairs for symbols of the specified type
    ///
    /// # Examples
    ///
    /// ```
    /// use hack_assembler::symbol_table::{SymbolTable, SymbolType};
    ///
    /// let table = SymbolTable::new();
    /// for (name, address) in table.iter_by_type(SymbolType::Predefined) {
    ///     println!("{} -> {}", name, address);
    /// }
    /// ```
    pub fn iter_by_type(&self, symbol_type: SymbolType) -> impl Iterator<Item = (&String, u16)> + '_ {
        self.entries.iter()
            .filter(move |(_, (_, typ))| *typ == symbol_type)
            .map(|(name, (address, _))| {
                let addr = match address {
                    SymbolAddress::Ram(addr) => *addr,
                    SymbolAddress::Rom(addr) => *addr,
                };
                (name, addr)
            })
    }
}

/// Errors that can occur during symbol table operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolError {
    /// A label with the same name already exists
    DuplicateLabel(String),
    /// A symbol wasn't found
    SymbolNotFound(String),
}