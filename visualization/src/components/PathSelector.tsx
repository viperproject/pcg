import React from 'react';

interface PathSelectorProps {
    paths: number[][];
    selectedPath: number;
    setSelectedPath: (pathIndex: number) => void;
    showPathBlocksOnly: boolean;
    setShowPathBlocksOnly: (show: boolean) => void;
}

const PathSelector: React.FC<PathSelectorProps> = ({
    paths,
    selectedPath,
    setSelectedPath,
    showPathBlocksOnly,
    setShowPathBlocksOnly,
}) => {
    if (paths.length === 0) {
        return null;
    }

    return (
        <>
            <label htmlFor="path-select">Select Path:</label>
            <select
                id="path-select"
                value={selectedPath}
                onChange={(e) => setSelectedPath(parseInt(e.target.value))}
            >
                {paths.map((path, index) => (
                    <option key={index} value={index}>
                        {path.map((p) => `bb${p}`).join(" -> ")}
                    </option>
                ))}
            </select>
            <br />
            <label>
                <input
                    type="checkbox"
                    checked={showPathBlocksOnly}
                    onChange={(e) => setShowPathBlocksOnly(e.target.checked)}
                />
                Show path blocks only
            </label>
            <br />
        </>
    );
};

export default PathSelector;
