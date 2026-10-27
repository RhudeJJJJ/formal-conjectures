/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4567 : Family 10 := level10.get ⟨490,by decide⟩
def sourceMap4567 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4567 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 2 2 v)
theorem sourceMap4567_checked : acceptsGraphIso
    (source (graph core4567) (root 10) 2 2) DegreeTwoThreeSpectrum6676.graph sourceMap4567=true := by decide +kernel
theorem fusedMap4567_checked : acceptsGraphIso
    (fused (graph core4567) (root 10) 2 2) DegreeTwoThreeSpectrum5955.graph fusedMap4567=true := by decide +kernel
theorem certified4567 : Certified (graph core4567) (root 10) 2 2 :=
  of_native_maps core4567 DegreeTwoThreeSpectrum6676.graph DegreeTwoThreeSpectrum5955.graph
    sourceMap4567 fusedMap4567 sourceMap4567_checked fusedMap4567_checked
    DegreeTwoThreeFiniteComparisons.comparison4567
#print axioms sourceMap4567_checked
#print axioms fusedMap4567_checked
#print axioms certified4567
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
