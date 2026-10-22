/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4679 : Family 10 := level10.get ⟨821,by decide⟩
def sourceMap4679 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4679 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4679_checked : acceptsGraphIso
    (source (graph core4679) (root 10) 2 2) DegreeTwoThreeSpectrum6789.graph sourceMap4679=true := by decide +kernel
theorem fusedMap4679_checked : acceptsGraphIso
    (fused (graph core4679) (root 10) 2 2) DegreeTwoThreeSpectrum5630.graph fusedMap4679=true := by decide +kernel
theorem certified4679 : Certified (graph core4679) (root 10) 2 2 :=
  of_native_maps core4679 DegreeTwoThreeSpectrum6789.graph DegreeTwoThreeSpectrum5630.graph
    sourceMap4679 fusedMap4679 sourceMap4679_checked fusedMap4679_checked
    DegreeTwoThreeFiniteComparisons.comparison4679
#print axioms sourceMap4679_checked
#print axioms fusedMap4679_checked
#print axioms certified4679
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
