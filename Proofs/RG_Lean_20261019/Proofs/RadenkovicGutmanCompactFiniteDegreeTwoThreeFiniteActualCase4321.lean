/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4321 : Family 9 := level9.get ⟨406,by decide⟩
def sourceMap4321 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4321 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4321_checked : acceptsGraphIso
    (source (graph core4321) (root 9) 2 2) DegreeTwoThreeSpectrum4788.graph sourceMap4321=true := by decide +kernel
theorem fusedMap4321_checked : acceptsGraphIso
    (fused (graph core4321) (root 9) 2 2) DegreeTwoThreeSpectrum4369.graph fusedMap4321=true := by decide +kernel
theorem certified4321 : Certified (graph core4321) (root 9) 2 2 :=
  of_native_maps core4321 DegreeTwoThreeSpectrum4788.graph DegreeTwoThreeSpectrum4369.graph
    sourceMap4321 fusedMap4321 sourceMap4321_checked fusedMap4321_checked
    DegreeTwoThreeFiniteComparisons.comparison4321
#print axioms sourceMap4321_checked
#print axioms fusedMap4321_checked
#print axioms certified4321
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
