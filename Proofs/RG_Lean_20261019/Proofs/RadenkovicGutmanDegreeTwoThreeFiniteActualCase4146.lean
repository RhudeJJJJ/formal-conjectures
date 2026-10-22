/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4146 : Family 8 := level8.get ⟨158,by decide⟩
def sourceMap4146 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,12,13,14,6,7,8,9,10,11] (sourceLabel 8 2 2 v)
def fusedMap4146 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4146_checked : acceptsGraphIso
    (source (graph core4146) (root 8) 2 2) DegreeTwoThreeSpectrum3591.graph sourceMap4146=true := by decide +kernel
theorem fusedMap4146_checked : acceptsGraphIso
    (fused (graph core4146) (root 8) 2 2) DegreeTwoThreeSpectrum2777.graph fusedMap4146=true := by decide +kernel
theorem certified4146 : Certified (graph core4146) (root 8) 2 2 :=
  of_native_maps core4146 DegreeTwoThreeSpectrum3591.graph DegreeTwoThreeSpectrum2777.graph
    sourceMap4146 fusedMap4146 sourceMap4146_checked fusedMap4146_checked
    DegreeTwoThreeFiniteComparisons.comparison4146
#print axioms sourceMap4146_checked
#print axioms fusedMap4146_checked
#print axioms certified4146
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
