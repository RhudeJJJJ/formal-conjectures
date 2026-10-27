/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4529 : Family 10 := level10.get ⟨387,by decide⟩
def sourceMap4529 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,9,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4529 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4529_checked : acceptsGraphIso
    (source (graph core4529) (root 10) 2 2) DegreeTwoThreeSpectrum6829.graph sourceMap4529=true := by decide +kernel
theorem fusedMap4529_checked : acceptsGraphIso
    (fused (graph core4529) (root 10) 2 2) DegreeTwoThreeSpectrum5721.graph fusedMap4529=true := by decide +kernel
theorem certified4529 : Certified (graph core4529) (root 10) 2 2 :=
  of_native_maps core4529 DegreeTwoThreeSpectrum6829.graph DegreeTwoThreeSpectrum5721.graph
    sourceMap4529 fusedMap4529 sourceMap4529_checked fusedMap4529_checked
    DegreeTwoThreeFiniteComparisons.comparison4529
#print axioms sourceMap4529_checked
#print axioms fusedMap4529_checked
#print axioms certified4529
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
