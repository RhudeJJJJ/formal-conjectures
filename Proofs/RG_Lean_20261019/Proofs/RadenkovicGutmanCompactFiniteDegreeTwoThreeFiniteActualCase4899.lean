/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4899 : Family 10 := level10.get ⟨1367,by decide⟩
def sourceMap4899 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4899 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4899_checked : acceptsGraphIso
    (source (graph core4899) (root 10) 2 2) DegreeTwoThreeSpectrum7446.graph sourceMap4899=true := by decide +kernel
theorem fusedMap4899_checked : acceptsGraphIso
    (fused (graph core4899) (root 10) 2 2) DegreeTwoThreeSpectrum6708.graph fusedMap4899=true := by decide +kernel
theorem certified4899 : Certified (graph core4899) (root 10) 2 2 :=
  of_native_maps core4899 DegreeTwoThreeSpectrum7446.graph DegreeTwoThreeSpectrum6708.graph
    sourceMap4899 fusedMap4899 sourceMap4899_checked fusedMap4899_checked
    DegreeTwoThreeFiniteComparisons.comparison4899
#print axioms sourceMap4899_checked
#print axioms fusedMap4899_checked
#print axioms certified4899
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
