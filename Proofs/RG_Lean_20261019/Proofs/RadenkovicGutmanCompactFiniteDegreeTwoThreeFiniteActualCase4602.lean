/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4602 : Family 10 := level10.get ⟨608,by decide⟩
def sourceMap4602 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4602 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4602_checked : acceptsGraphIso
    (source (graph core4602) (root 10) 2 2) DegreeTwoThreeSpectrum7256.graph sourceMap4602=true := by decide +kernel
theorem fusedMap4602_checked : acceptsGraphIso
    (fused (graph core4602) (root 10) 2 2) DegreeTwoThreeSpectrum5287.graph fusedMap4602=true := by decide +kernel
theorem certified4602 : Certified (graph core4602) (root 10) 2 2 :=
  of_native_maps core4602 DegreeTwoThreeSpectrum7256.graph DegreeTwoThreeSpectrum5287.graph
    sourceMap4602 fusedMap4602 sourceMap4602_checked fusedMap4602_checked
    DegreeTwoThreeFiniteComparisons.comparison4602
#print axioms sourceMap4602_checked
#print axioms fusedMap4602_checked
#print axioms certified4602
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
