/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4532 : Family 10 := level10.get ⟨397,by decide⟩
def sourceMap4532 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4532 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4532_checked : acceptsGraphIso
    (source (graph core4532) (root 10) 2 2) DegreeTwoThreeSpectrum6843.graph sourceMap4532=true := by decide +kernel
theorem fusedMap4532_checked : acceptsGraphIso
    (fused (graph core4532) (root 10) 2 2) DegreeTwoThreeSpectrum5748.graph fusedMap4532=true := by decide +kernel
theorem certified4532 : Certified (graph core4532) (root 10) 2 2 :=
  of_native_maps core4532 DegreeTwoThreeSpectrum6843.graph DegreeTwoThreeSpectrum5748.graph
    sourceMap4532 fusedMap4532 sourceMap4532_checked fusedMap4532_checked
    DegreeTwoThreeFiniteComparisons.comparison4532
#print axioms sourceMap4532_checked
#print axioms fusedMap4532_checked
#print axioms certified4532
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
