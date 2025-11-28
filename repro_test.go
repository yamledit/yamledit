package yamledit

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestRepro(t *testing.T) {
	yamlInput := `
pipelineName: old-name
pipelineConfig:
  pipelineProcess:
    - processName: process-1
      plugin:
        name: flinkstream
`
	doc, err := Parse([]byte(yamlInput))
	require.NoError(t, err)

	// Applying a patch to a deep element in a list of maps
	patches := []map[string]interface{}{
		{
			"op":    "replace",
			"path":  "/pipelineConfig/pipelineProcess/0/plugin/name",
			"value": "new-plugin-name",
		},
	}
	patchJSON, err := json.Marshal(patches)
	require.NoError(t, err)

	err = ApplyJSONPatchBytes(doc, patchJSON)
	require.NoError(t, err)

	output, err := Marshal(doc)
	require.NoError(t, err)

	actualStr := string(output)

	// Check that the output does NOT contain the corrupted "key/value" sequence style
	assert.NotContains(t, actualStr, "- key: processName", "Output should not be converted to a key/value sequence")

	// Check that it DOES contain the expected mapping style
	assert.Contains(t, actualStr, "processName: process-1", "Output should maintain original mapping style")
	assert.Contains(t, actualStr, "name: new-plugin-name", "Output should contain the updated value in mapping style")
}
