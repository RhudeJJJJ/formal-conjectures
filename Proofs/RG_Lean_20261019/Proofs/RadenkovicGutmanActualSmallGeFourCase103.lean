/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core103 : Family 7 := level7.get ⟨113,by decide⟩
def sourceMap103 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,7,8,9,10,11,3,4,5,6] (sourceLabel 7 1 1 v)
def fusedMap103 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap103_checked : acceptsGraphIso
    (source (graph core103) (root 7) 1 1) SmallGeFourSpectrum231.graph
      sourceMap103=true := by decide +kernel
theorem fusedMap103_checked : acceptsGraphIso
    (fused (graph core103) (root 7) 1 1) SmallGeFourSpectrum180.graph
      fusedMap103=true := by decide +kernel
theorem certified103 : Certified (graph core103) (root 7) 1 1 :=
  of_native_maps core103 SmallGeFourSpectrum231.graph SmallGeFourSpectrum180.graph
    sourceMap103 fusedMap103 sourceMap103_checked fusedMap103_checked
    SmallGeFourComparisons.comparison103
#print axioms sourceMap103_checked
#print axioms fusedMap103_checked
#print axioms certified103
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
