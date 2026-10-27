/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4288 : Family 9 := level9.get ⟨320,by decide⟩
def sourceMap4288 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4288 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4288_checked : acceptsGraphIso
    (source (graph core4288) (root 9) 2 2) DegreeTwoThreeSpectrum4676.graph sourceMap4288=true := by decide +kernel
theorem fusedMap4288_checked : acceptsGraphIso
    (fused (graph core4288) (root 9) 2 2) DegreeTwoThreeSpectrum4181.graph fusedMap4288=true := by decide +kernel
theorem certified4288 : Certified (graph core4288) (root 9) 2 2 :=
  of_native_maps core4288 DegreeTwoThreeSpectrum4676.graph DegreeTwoThreeSpectrum4181.graph
    sourceMap4288 fusedMap4288 sourceMap4288_checked fusedMap4288_checked
    DegreeTwoThreeFiniteComparisons.comparison4288
#print axioms sourceMap4288_checked
#print axioms fusedMap4288_checked
#print axioms certified4288
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
