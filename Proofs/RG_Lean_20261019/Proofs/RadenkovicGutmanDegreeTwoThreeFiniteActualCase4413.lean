/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4413 : Family 9 := level9.get ⟨632,by decide⟩
def sourceMap4413 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4413 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4413_checked : acceptsGraphIso
    (source (graph core4413) (root 9) 2 2) DegreeTwoThreeSpectrum4940.graph sourceMap4413=true := by decide +kernel
theorem fusedMap4413_checked : acceptsGraphIso
    (fused (graph core4413) (root 9) 2 2) DegreeTwoThreeSpectrum4392.graph fusedMap4413=true := by decide +kernel
theorem certified4413 : Certified (graph core4413) (root 9) 2 2 :=
  of_native_maps core4413 DegreeTwoThreeSpectrum4940.graph DegreeTwoThreeSpectrum4392.graph
    sourceMap4413 fusedMap4413 sourceMap4413_checked fusedMap4413_checked
    DegreeTwoThreeFiniteComparisons.comparison4413
#print axioms sourceMap4413_checked
#print axioms fusedMap4413_checked
#print axioms certified4413
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
