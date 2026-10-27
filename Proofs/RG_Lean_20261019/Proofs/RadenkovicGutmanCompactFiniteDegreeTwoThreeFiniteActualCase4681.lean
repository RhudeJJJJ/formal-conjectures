/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4681 : Family 10 := level10.get ⟨823,by decide⟩
def sourceMap4681 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4681 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4681_checked : acceptsGraphIso
    (source (graph core4681) (root 10) 2 2) DegreeTwoThreeSpectrum7427.graph sourceMap4681=true := by decide +kernel
theorem fusedMap4681_checked : acceptsGraphIso
    (fused (graph core4681) (root 10) 2 2) DegreeTwoThreeSpectrum5632.graph fusedMap4681=true := by decide +kernel
theorem certified4681 : Certified (graph core4681) (root 10) 2 2 :=
  of_native_maps core4681 DegreeTwoThreeSpectrum7427.graph DegreeTwoThreeSpectrum5632.graph
    sourceMap4681 fusedMap4681 sourceMap4681_checked fusedMap4681_checked
    DegreeTwoThreeFiniteComparisons.comparison4681
#print axioms sourceMap4681_checked
#print axioms fusedMap4681_checked
#print axioms certified4681
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
