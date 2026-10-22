/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4517 : Family 10 := level10.get ⟨349,by decide⟩
def sourceMap4517 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4517 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4517_checked : acceptsGraphIso
    (source (graph core4517) (root 10) 2 2) DegreeTwoThreeSpectrum6774.graph sourceMap4517=true := by decide +kernel
theorem fusedMap4517_checked : acceptsGraphIso
    (fused (graph core4517) (root 10) 2 2) DegreeTwoThreeSpectrum5618.graph fusedMap4517=true := by decide +kernel
theorem certified4517 : Certified (graph core4517) (root 10) 2 2 :=
  of_native_maps core4517 DegreeTwoThreeSpectrum6774.graph DegreeTwoThreeSpectrum5618.graph
    sourceMap4517 fusedMap4517 sourceMap4517_checked fusedMap4517_checked
    DegreeTwoThreeFiniteComparisons.comparison4517
#print axioms sourceMap4517_checked
#print axioms fusedMap4517_checked
#print axioms certified4517
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
