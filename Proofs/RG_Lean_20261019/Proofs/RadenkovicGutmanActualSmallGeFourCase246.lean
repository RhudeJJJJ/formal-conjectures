/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core246 : Family 9 := level9.get ⟨718,by decide⟩
def sourceMap246 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap246 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap246_checked : acceptsGraphIso
    (source (graph core246) (root 9) 0 0) SmallGeFourSpectrum233.graph
      sourceMap246=true := by decide +kernel
theorem fusedMap246_checked : acceptsGraphIso
    (fused (graph core246) (root 9) 0 0) SmallGeFourSpectrum197.graph
      fusedMap246=true := by decide +kernel
theorem certified246 : Certified (graph core246) (root 9) 0 0 :=
  of_native_maps core246 SmallGeFourSpectrum233.graph SmallGeFourSpectrum197.graph
    sourceMap246 fusedMap246 sourceMap246_checked fusedMap246_checked
    SmallGeFourComparisons.comparison246
#print axioms sourceMap246_checked
#print axioms fusedMap246_checked
#print axioms certified246
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
