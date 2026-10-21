/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core223 : Family 9 := level9.get ⟨683,by decide⟩
def sourceMap223 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap223 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,8,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap223_checked : acceptsGraphIso
    (source (graph core223) (root 9) 0 0) SmallGeFourSpectrum141.graph
      sourceMap223=true := by decide +kernel
theorem fusedMap223_checked : acceptsGraphIso
    (fused (graph core223) (root 9) 0 0) SmallGeFourSpectrum140.graph
      fusedMap223=true := by decide +kernel
theorem certified223 : Certified (graph core223) (root 9) 0 0 :=
  of_native_maps core223 SmallGeFourSpectrum141.graph SmallGeFourSpectrum140.graph
    sourceMap223 fusedMap223 sourceMap223_checked fusedMap223_checked
    SmallGeFourComparisons.comparison223
#print axioms sourceMap223_checked
#print axioms fusedMap223_checked
#print axioms certified223
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
