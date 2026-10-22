/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4006 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap4006 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,8,9,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4006 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4006_checked : acceptsGraphIso
    (source (graph core4006) (root 6) 1 6) DegreeTwoThreeSpectrum4421.graph sourceMap4006=true := by decide +kernel
theorem fusedMap4006_checked : acceptsGraphIso
    (fused (graph core4006) (root 6) 1 6) DegreeTwoThreeSpectrum3991.graph fusedMap4006=true := by decide +kernel
theorem certified4006 : Certified (graph core4006) (root 6) 1 6 :=
  of_native_maps core4006 DegreeTwoThreeSpectrum4421.graph DegreeTwoThreeSpectrum3991.graph
    sourceMap4006 fusedMap4006 sourceMap4006_checked fusedMap4006_checked
    DegreeTwoThreeFiniteComparisons.comparison4006
#print axioms sourceMap4006_checked
#print axioms fusedMap4006_checked
#print axioms certified4006
def sourceMap4006swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,1,0,11,12,13,14,15,8,9] (sourceLabel 6 6 1 v)
def fusedMap4006swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4006swap_checked : acceptsGraphIso
    (source (graph core4006) (root 6) 6 1) DegreeTwoThreeSpectrum4421.graph sourceMap4006swap=true := by decide +kernel
theorem fusedMap4006swap_checked : acceptsGraphIso
    (fused (graph core4006) (root 6) 6 1) DegreeTwoThreeSpectrum3991.graph fusedMap4006swap=true := by decide +kernel
theorem certified4006swap : Certified (graph core4006) (root 6) 6 1 :=
  of_native_maps core4006 DegreeTwoThreeSpectrum4421.graph DegreeTwoThreeSpectrum3991.graph
    sourceMap4006swap fusedMap4006swap sourceMap4006swap_checked fusedMap4006swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4006
#print axioms sourceMap4006swap_checked
#print axioms fusedMap4006swap_checked
#print axioms certified4006swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
