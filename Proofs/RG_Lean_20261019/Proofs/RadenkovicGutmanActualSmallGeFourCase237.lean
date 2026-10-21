/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core237 : Family 9 := level9.get ⟨709,by decide⟩
def sourceMap237 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap237 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap237_checked : acceptsGraphIso
    (source (graph core237) (root 9) 0 0) SmallGeFourSpectrum224.graph
      sourceMap237=true := by decide +kernel
theorem fusedMap237_checked : acceptsGraphIso
    (fused (graph core237) (root 9) 0 0) SmallGeFourSpectrum223.graph
      fusedMap237=true := by decide +kernel
theorem certified237 : Certified (graph core237) (root 9) 0 0 :=
  of_native_maps core237 SmallGeFourSpectrum224.graph SmallGeFourSpectrum223.graph
    sourceMap237 fusedMap237 sourceMap237_checked fusedMap237_checked
    SmallGeFourComparisons.comparison237
#print axioms sourceMap237_checked
#print axioms fusedMap237_checked
#print axioms certified237
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
