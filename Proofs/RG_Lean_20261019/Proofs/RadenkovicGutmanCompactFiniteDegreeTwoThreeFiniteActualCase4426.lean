/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4426 : Family 9 := level9.get ⟨667,by decide⟩
def sourceMap4426 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,11,12,13,14,15,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4426 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4426_checked : acceptsGraphIso
    (source (graph core4426) (root 9) 2 2) DegreeTwoThreeSpectrum4953.graph sourceMap4426=true := by decide +kernel
theorem fusedMap4426_checked : acceptsGraphIso
    (fused (graph core4426) (root 9) 2 2) DegreeTwoThreeSpectrum4487.graph fusedMap4426=true := by decide +kernel
theorem certified4426 : Certified (graph core4426) (root 9) 2 2 :=
  of_native_maps core4426 DegreeTwoThreeSpectrum4953.graph DegreeTwoThreeSpectrum4487.graph
    sourceMap4426 fusedMap4426 sourceMap4426_checked fusedMap4426_checked
    DegreeTwoThreeFiniteComparisons.comparison4426
#print axioms sourceMap4426_checked
#print axioms fusedMap4426_checked
#print axioms certified4426
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
