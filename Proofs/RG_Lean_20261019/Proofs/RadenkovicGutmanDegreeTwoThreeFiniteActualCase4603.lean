/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4603 : Family 10 := level10.get ⟨609,by decide⟩
def sourceMap4603 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,14,15,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4603 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4603_checked : acceptsGraphIso
    (source (graph core4603) (root 10) 2 2) DegreeTwoThreeSpectrum7254.graph sourceMap4603=true := by decide +kernel
theorem fusedMap4603_checked : acceptsGraphIso
    (fused (graph core4603) (root 10) 2 2) DegreeTwoThreeSpectrum5289.graph fusedMap4603=true := by decide +kernel
theorem certified4603 : Certified (graph core4603) (root 10) 2 2 :=
  of_native_maps core4603 DegreeTwoThreeSpectrum7254.graph DegreeTwoThreeSpectrum5289.graph
    sourceMap4603 fusedMap4603 sourceMap4603_checked fusedMap4603_checked
    DegreeTwoThreeFiniteComparisons.comparison4603
#print axioms sourceMap4603_checked
#print axioms fusedMap4603_checked
#print axioms certified4603
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
