/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripParityBridge

/-! Joint verification of original low-strip scalar integration and actual-graph
specialization. The original polynomial sign comparisons remain premises. -/
namespace Gebendorfer.RadenkovicGutman.LowStripCombined

#check @LowStripPrimitive.integral_eight_thirds
#check @LowStripPrimitive.original_graph_lowstrip_lower
#check @QuadraticDisk.convex_nonneg
#check @LowStripGeometry.tangent_graph_lower_of_actual_signs
#print axioms LowStripPrimitive.original_graph_lowstrip_lower
#print axioms LowStripGeometry.tangent_graph_lower_of_actual_signs
#check @LowStripCoordinates.tangent_coordinate_exists
#check @LowStripConstantGeometry.lead_pos
#print axioms LowStripSignAssembly.strict_fusion_of_original_sign_families
#print axioms HighDegreeInputFromSigns.normalized_lower_of_original_sign_families
#print axioms LowStripParityBridge.original_normalized_target_of_parity_families

end Gebendorfer.RadenkovicGutman.LowStripCombined
