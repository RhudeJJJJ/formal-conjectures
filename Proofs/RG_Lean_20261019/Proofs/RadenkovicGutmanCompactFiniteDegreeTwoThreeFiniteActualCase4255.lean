/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4255 : Family 9 := level9.get ⟨233,by decide⟩
def sourceMap4255 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4255 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4255_checked : acceptsGraphIso
    (source (graph core4255) (root 9) 2 2) DegreeTwoThreeSpectrum4850.graph sourceMap4255=true := by decide +kernel
theorem fusedMap4255_checked : acceptsGraphIso
    (fused (graph core4255) (root 9) 2 2) DegreeTwoThreeSpectrum4025.graph fusedMap4255=true := by decide +kernel
theorem certified4255 : Certified (graph core4255) (root 9) 2 2 :=
  of_native_maps core4255 DegreeTwoThreeSpectrum4850.graph DegreeTwoThreeSpectrum4025.graph
    sourceMap4255 fusedMap4255 sourceMap4255_checked fusedMap4255_checked
    DegreeTwoThreeFiniteComparisons.comparison4255
#print axioms sourceMap4255_checked
#print axioms fusedMap4255_checked
#print axioms certified4255
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
