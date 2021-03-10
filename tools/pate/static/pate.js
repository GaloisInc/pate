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
                  height: '500px'
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
        ],
        layout: { name: 'breadthfirst',
                  fit: true,
                  circle: false,
                  grid: true
                }
    });

    cy.nodeHtmlLabel([{
        query: 'node',
        tpl: function(data) {
            return '<pre class="graph-node-label">' + data.text + '</pre>';
        }
    }], {enablePointerEvents: true});
}
