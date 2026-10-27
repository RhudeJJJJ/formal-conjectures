/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4639 : Family 10 := level10.get ⟨711,by decide⟩
def sourceMap4639 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4639 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4639_checked : acceptsGraphIso
    (source (graph core4639) (root 10) 2 2) DegreeTwoThreeSpectrum7368.graph sourceMap4639=true := by decide +kernel
theorem fusedMap4639_checked : acceptsGraphIso
    (fused (graph core4639) (root 10) 2 2) DegreeTwoThreeSpectrum5454.graph fusedMap4639=true := by decide +kernel
theorem certified4639 : Certified (graph core4639) (root 10) 2 2 :=
  of_native_maps core4639 DegreeTwoThreeSpectrum7368.graph DegreeTwoThreeSpectrum5454.graph
    sourceMap4639 fusedMap4639 sourceMap4639_checked fusedMap4639_checked
    DegreeTwoThreeFiniteComparisons.comparison4639
#print axioms sourceMap4639_checked
#print axioms fusedMap4639_checked
#print axioms certified4639
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
