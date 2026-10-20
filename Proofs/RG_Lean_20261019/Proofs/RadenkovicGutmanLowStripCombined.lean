/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripGeometry
import Proofs.RadenkovicGutmanLowStripAssembly

/-! Joint verification of original low-strip scalar integration and actual-graph
specialization. The original polynomial sign comparisons remain premises. -/
namespace Gebendorfer.RadenkovicGutman.LowStripCombined

#check @LowStripPrimitive.integral_eight_thirds
#check @LowStripPrimitive.original_graph_lowstrip_lower
#check @QuadraticDisk.convex_nonneg
#check @LowStripGeometry.tangent_graph_lower_of_actual_signs
#print axioms LowStripPrimitive.original_graph_lowstrip_lower
#print axioms LowStripGeometry.tangent_graph_lower_of_actual_signs

end Gebendorfer.RadenkovicGutman.LowStripCombined
