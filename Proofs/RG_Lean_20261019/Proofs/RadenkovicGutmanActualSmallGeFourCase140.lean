/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core140 : Family 8 := level8.get ⟨261,by decide⟩
def sourceMap140 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap140 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,3,4,7,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap140_checked : acceptsGraphIso
    (source (graph core140) (root 8) 0 0) SmallGeFourSpectrum056.graph
      sourceMap140=true := by decide +kernel
theorem fusedMap140_checked : acceptsGraphIso
    (fused (graph core140) (root 8) 0 0) SmallGeFourSpectrum055.graph
      fusedMap140=true := by decide +kernel
theorem certified140 : Certified (graph core140) (root 8) 0 0 :=
  of_native_maps core140 SmallGeFourSpectrum056.graph SmallGeFourSpectrum055.graph
    sourceMap140 fusedMap140 sourceMap140_checked fusedMap140_checked
    SmallGeFourComparisons.comparison140
#print axioms sourceMap140_checked
#print axioms fusedMap140_checked
#print axioms certified140
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
