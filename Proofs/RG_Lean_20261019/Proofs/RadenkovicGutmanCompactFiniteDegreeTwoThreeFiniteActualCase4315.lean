/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4315 : Family 9 := level9.get ⟨395,by decide⟩
def sourceMap4315 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4315 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4315_checked : acceptsGraphIso
    (source (graph core4315) (root 9) 2 2) DegreeTwoThreeSpectrum4771.graph sourceMap4315=true := by decide +kernel
theorem fusedMap4315_checked : acceptsGraphIso
    (fused (graph core4315) (root 9) 2 2) DegreeTwoThreeSpectrum4348.graph fusedMap4315=true := by decide +kernel
theorem certified4315 : Certified (graph core4315) (root 9) 2 2 :=
  of_native_maps core4315 DegreeTwoThreeSpectrum4771.graph DegreeTwoThreeSpectrum4348.graph
    sourceMap4315 fusedMap4315 sourceMap4315_checked fusedMap4315_checked
    DegreeTwoThreeFiniteComparisons.comparison4315
#print axioms sourceMap4315_checked
#print axioms fusedMap4315_checked
#print axioms certified4315
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
