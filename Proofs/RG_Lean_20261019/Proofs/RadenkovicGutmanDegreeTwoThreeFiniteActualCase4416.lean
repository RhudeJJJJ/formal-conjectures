/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4416 : Family 9 := level9.get ⟨638,by decide⟩
def sourceMap4416 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4416 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4416_checked : acceptsGraphIso
    (source (graph core4416) (root 9) 2 2) DegreeTwoThreeSpectrum4943.graph sourceMap4416=true := by decide +kernel
theorem fusedMap4416_checked : acceptsGraphIso
    (fused (graph core4416) (root 9) 2 2) DegreeTwoThreeSpectrum4403.graph fusedMap4416=true := by decide +kernel
theorem certified4416 : Certified (graph core4416) (root 9) 2 2 :=
  of_native_maps core4416 DegreeTwoThreeSpectrum4943.graph DegreeTwoThreeSpectrum4403.graph
    sourceMap4416 fusedMap4416 sourceMap4416_checked fusedMap4416_checked
    DegreeTwoThreeFiniteComparisons.comparison4416
#print axioms sourceMap4416_checked
#print axioms fusedMap4416_checked
#print axioms certified4416
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
