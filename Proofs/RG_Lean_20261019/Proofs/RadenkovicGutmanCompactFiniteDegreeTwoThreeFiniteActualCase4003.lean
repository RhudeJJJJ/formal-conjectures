/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4003 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap4003 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,8,9,1,0,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4003 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4003_checked : acceptsGraphIso
    (source (graph core4003) (root 6) 1 6) DegreeTwoThreeSpectrum4241.graph sourceMap4003=true := by decide +kernel
theorem fusedMap4003_checked : acceptsGraphIso
    (fused (graph core4003) (root 6) 1 6) DegreeTwoThreeSpectrum3907.graph fusedMap4003=true := by decide +kernel
theorem certified4003 : Certified (graph core4003) (root 6) 1 6 :=
  of_native_maps core4003 DegreeTwoThreeSpectrum4241.graph DegreeTwoThreeSpectrum3907.graph
    sourceMap4003 fusedMap4003 sourceMap4003_checked fusedMap4003_checked
    DegreeTwoThreeFiniteComparisons.comparison4003
#print axioms sourceMap4003_checked
#print axioms fusedMap4003_checked
#print axioms certified4003
def sourceMap4003swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,10,1,0,11,12,13,14,15,8,9] (sourceLabel 6 6 1 v)
def fusedMap4003swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4003swap_checked : acceptsGraphIso
    (source (graph core4003) (root 6) 6 1) DegreeTwoThreeSpectrum4241.graph sourceMap4003swap=true := by decide +kernel
theorem fusedMap4003swap_checked : acceptsGraphIso
    (fused (graph core4003) (root 6) 6 1) DegreeTwoThreeSpectrum3907.graph fusedMap4003swap=true := by decide +kernel
theorem certified4003swap : Certified (graph core4003) (root 6) 6 1 :=
  of_native_maps core4003 DegreeTwoThreeSpectrum4241.graph DegreeTwoThreeSpectrum3907.graph
    sourceMap4003swap fusedMap4003swap sourceMap4003swap_checked fusedMap4003swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4003
#print axioms sourceMap4003swap_checked
#print axioms fusedMap4003swap_checked
#print axioms certified4003swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
