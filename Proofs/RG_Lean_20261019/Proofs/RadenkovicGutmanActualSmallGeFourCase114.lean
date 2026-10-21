/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core114 : Family 8 := level8.get ⟨178,by decide⟩
def sourceMap114 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,7,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap114 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap114_checked : acceptsGraphIso
    (source (graph core114) (root 8) 0 0) SmallGeFourSpectrum041.graph
      sourceMap114=true := by decide +kernel
theorem fusedMap114_checked : acceptsGraphIso
    (fused (graph core114) (root 8) 0 0) SmallGeFourSpectrum065.graph
      fusedMap114=true := by decide +kernel
theorem certified114 : Certified (graph core114) (root 8) 0 0 :=
  of_native_maps core114 SmallGeFourSpectrum041.graph SmallGeFourSpectrum065.graph
    sourceMap114 fusedMap114 sourceMap114_checked fusedMap114_checked
    SmallGeFourComparisons.comparison114
#print axioms sourceMap114_checked
#print axioms fusedMap114_checked
#print axioms certified114
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
