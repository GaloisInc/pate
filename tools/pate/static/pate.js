/**
  * Scroll the selected node body (the pre tag containing the text) if there is only one selected
  *
  * If this function scrolls the single selected node, it prevents the page from scrolling at the same time.
  */
function scrollSelectedGraphNodeLabel(cy, e, amount) {
    var sel = cy.$(':selected');
    if(sel.length == 1) {
        var pre = document.getElementById('pre-' + sel[0].data().id);
        pre.scrollBy(0, amount);
        e.stopPropagation();
        e.preventDefault();
    }
}

/**
 * Initialize a graph in the given div with the given data (which corresponds to a cytoscape elements map)
 *
 * @param{string} divId
 * @param{Object} graphData
 */
function initializeGraphIn(divId, graphData) {
    var cy = cytoscape({
        container: document.getElementById(divId),
        elements: graphData,
        style: [
            { selector: 'node',
              style: {
                  shape: 'round-rectangle',
                  width: '400px',
                  height: '500px',
                  events: 'yes',
                  'text-events': 'yes'
              }
            },
            { selector: 'edge',
              style: {
                  'width': 3,
                  'curve-style': 'bezier',
                  'line-color': '#ccc',
                  'target-arrow-color': '#ccc',
                  'target-arrow-shape': 'triangle'
              }
            }
        ]
    });


    cy.nodeHtmlLabel([{
        query: 'node',
        tpl: function(data) {
            return '<pre id="pre-' + data.id + '" class="graph-node-label">' + data.text + '</pre>';
        }
    }], {enablePointerEvents: true});

    cy.layout({ name: 'dagre'
              }).run();

    document.addEventListener('keydown', function(e) {
        if(e.key == 'ArrowDown') {
            scrollSelectedGraphNodeLabel(cy, e, 20);
        } else if(e.key == 'ArrowUp') {
            scrollSelectedGraphNodeLabel(cy, e, -20);
        }
    });
}

