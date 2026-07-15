package yamledit

import (
	"runtime"
	"strings"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"
	"gopkg.in/yaml.v3"
)

// This test is most valuable under -race. The writer models a state-aware edit
// converting a mapping value to a scalar and back while JSON Patch is handed the
// same stable node pointer. Patch target classification must share st.mu with the
// writer; otherwise its initial node.Kind read races.
func TestApplyJSONPatchClassifiesRegisteredMappingHandleUnderLock(t *testing.T) {
	doc, err := Parse([]byte("target:\n  value: old\n"))
	require.NoError(t, err)
	target := doc.Content[0].Content[1]
	st, ok := lookup(doc)
	require.True(t, ok)

	const iterations = 250
	start := make(chan struct{})
	errs := make(chan error, iterations)
	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		defer wg.Done()
		<-start
		for i := 0; i < iterations; i++ {
			st.mu.Lock()
			if i%2 == 0 {
				target.Kind = yaml.ScalarNode
			} else {
				target.Kind = yaml.MappingNode
			}
			st.mu.Unlock()
			runtime.Gosched()
		}
		st.mu.Lock()
		target.Kind = yaml.MappingNode
		st.mu.Unlock()
	}()
	go func() {
		defer wg.Done()
		<-start
		for i := 0; i < iterations; i++ {
			err := ApplyJSONPatchBytes(target, []byte(`[]`))
			if err != nil && !strings.Contains(err.Error(), "requires a DocumentNode or MappingNode") {
				errs <- err
			}
			runtime.Gosched()
		}
	}()
	close(start)
	wg.Wait()
	close(errs)
	for err := range errs {
		require.NoError(t, err)
	}

	require.Equal(t, yaml.MappingNode, target.Kind)
}

// A mapping value is converted in place by the scalar setter and EnsurePath.
// Every mapping-handle mutator must discover ownership before reading Kind and
// then revalidate the handle under the shared document lock.
func TestMappingHandleMutatorsClassifyUnderLock(t *testing.T) {
	doc, err := Parse([]byte("target:\n  value: old\n"))
	require.NoError(t, err)
	root := doc.Content[0]
	target := root.Content[1]

	const iterations = 200
	start := make(chan struct{})
	var wg sync.WaitGroup
	for worker := 0; worker < 4; worker++ {
		worker := worker
		wg.Add(1)
		go func() {
			defer wg.Done()
			<-start
			for i := 0; i < iterations; i++ {
				switch worker {
				case 0:
					SetScalarString(target, "value", "updated")
				case 1:
					DeleteKey(target, "temporary")
				case 2:
					_ = EnsurePath(target, "nested")
				case 3:
					SetScalarString(root, "target", "temporary scalar")
					_ = EnsurePath(root, "target")
				}
				runtime.Gosched()
			}
		}()
	}
	close(start)
	wg.Wait()

	finalTarget := EnsurePath(root, "target")
	require.NotNil(t, finalTarget)
	SetScalarString(finalTarget, "final", "yes")
	out, err := Marshal(doc)
	require.NoError(t, err)
	var got map[string]map[string]any
	require.NoError(t, yaml.Unmarshal(out, &got), "output:\n%s", out)
	require.Equal(t, "yes", got["target"]["final"])
}
