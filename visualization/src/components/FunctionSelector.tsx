import React from "react";

interface FunctionSelectorProps {
  functions: Record<string, string>;
  selectedFunction: string;
  onChange: (selectedFunction: string) => void;
}

const FunctionSelector: React.FC<FunctionSelectorProps> = ({
  functions,
  selectedFunction,
  onChange,
}) => {
  return (
    <>
      <label htmlFor="function-select">Select Function:</label>
      <select
        id="function-select"
        value={selectedFunction}
        onChange={(e) => {
          onChange(e.target.value);
        }}
      >
        {Object.keys(functions)
          .sort((a, b) => functions[a].localeCompare(functions[b]))
          .map((func) => (
            <option key={func} value={func}>
              {functions[func]}
            </option>
          ))}
      </select>
    </>
  );
};

export default FunctionSelector;
