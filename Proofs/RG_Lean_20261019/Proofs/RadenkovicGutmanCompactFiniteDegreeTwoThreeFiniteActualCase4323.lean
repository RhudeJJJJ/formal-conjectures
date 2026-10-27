/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4323 : Family 9 := level9.get ⟨408,by decide⟩
def sourceMap4323 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4323 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4323_checked : acceptsGraphIso
    (source (graph core4323) (root 9) 2 2) DegreeTwoThreeSpectrum4781.graph sourceMap4323=true := by decide +kernel
theorem fusedMap4323_checked : acceptsGraphIso
    (fused (graph core4323) (root 9) 2 2) DegreeTwoThreeSpectrum4373.graph fusedMap4323=true := by decide +kernel
theorem certified4323 : Certified (graph core4323) (root 9) 2 2 :=
  of_native_maps core4323 DegreeTwoThreeSpectrum4781.graph DegreeTwoThreeSpectrum4373.graph
    sourceMap4323 fusedMap4323 sourceMap4323_checked fusedMap4323_checked
    DegreeTwoThreeFiniteComparisons.comparison4323
#print axioms sourceMap4323_checked
#print axioms fusedMap4323_checked
#print axioms certified4323
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
