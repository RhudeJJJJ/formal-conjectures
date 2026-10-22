/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4009 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap4009 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4009 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4009_checked : acceptsGraphIso
    (source (graph core4009) (root 6) 1 6) DegreeTwoThreeSpectrum4544.graph sourceMap4009=true := by decide +kernel
theorem fusedMap4009_checked : acceptsGraphIso
    (fused (graph core4009) (root 6) 1 6) DegreeTwoThreeSpectrum4062.graph fusedMap4009=true := by decide +kernel
theorem certified4009 : Certified (graph core4009) (root 6) 1 6 :=
  of_native_maps core4009 DegreeTwoThreeSpectrum4544.graph DegreeTwoThreeSpectrum4062.graph
    sourceMap4009 fusedMap4009 sourceMap4009_checked fusedMap4009_checked
    DegreeTwoThreeFiniteComparisons.comparison4009
#print axioms sourceMap4009_checked
#print axioms fusedMap4009_checked
#print axioms certified4009
def sourceMap4009swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,11,12,13,14,15,9,10] (sourceLabel 6 6 1 v)
def fusedMap4009swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4009swap_checked : acceptsGraphIso
    (source (graph core4009) (root 6) 6 1) DegreeTwoThreeSpectrum4544.graph sourceMap4009swap=true := by decide +kernel
theorem fusedMap4009swap_checked : acceptsGraphIso
    (fused (graph core4009) (root 6) 6 1) DegreeTwoThreeSpectrum4062.graph fusedMap4009swap=true := by decide +kernel
theorem certified4009swap : Certified (graph core4009) (root 6) 6 1 :=
  of_native_maps core4009 DegreeTwoThreeSpectrum4544.graph DegreeTwoThreeSpectrum4062.graph
    sourceMap4009swap fusedMap4009swap sourceMap4009swap_checked fusedMap4009swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4009
#print axioms sourceMap4009swap_checked
#print axioms fusedMap4009swap_checked
#print axioms certified4009swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
