/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4421 : Family 9 := level9.get ⟨651,by decide⟩
def sourceMap4421 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4421 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4421_checked : acceptsGraphIso
    (source (graph core4421) (root 9) 2 2) DegreeTwoThreeSpectrum4948.graph sourceMap4421=true := by decide +kernel
theorem fusedMap4421_checked : acceptsGraphIso
    (fused (graph core4421) (root 9) 2 2) DegreeTwoThreeSpectrum4440.graph fusedMap4421=true := by decide +kernel
theorem certified4421 : Certified (graph core4421) (root 9) 2 2 :=
  of_native_maps core4421 DegreeTwoThreeSpectrum4948.graph DegreeTwoThreeSpectrum4440.graph
    sourceMap4421 fusedMap4421 sourceMap4421_checked fusedMap4421_checked
    DegreeTwoThreeFiniteComparisons.comparison4421
#print axioms sourceMap4421_checked
#print axioms fusedMap4421_checked
#print axioms certified4421
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
