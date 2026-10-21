/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0282 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0282 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0282 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0282_checked : acceptsGraphIso
    (source (graph core0282) (root 6) 1 2) DegreeOneSmallSpectrum494.graph sourceMap0282=true := by decide +kernel
theorem fusedMap0282_checked : acceptsGraphIso
    (fused (graph core0282) (root 6) 1 2) DegreeOneSmallSpectrum378.graph fusedMap0282=true := by decide +kernel
theorem certified0282 : Certified (graph core0282) (root 6) 1 2 :=
  of_native_maps core0282 DegreeOneSmallSpectrum494.graph DegreeOneSmallSpectrum378.graph
    sourceMap0282 fusedMap0282 sourceMap0282_checked fusedMap0282_checked
    DegreeOneSmallComparisons.comparison0282
#print axioms sourceMap0282_checked
#print axioms fusedMap0282_checked
#print axioms certified0282
def sourceMap0282swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0282swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0282swap_checked : acceptsGraphIso
    (source (graph core0282) (root 6) 2 1) DegreeOneSmallSpectrum494.graph sourceMap0282swap=true := by decide +kernel
theorem fusedMap0282swap_checked : acceptsGraphIso
    (fused (graph core0282) (root 6) 2 1) DegreeOneSmallSpectrum378.graph fusedMap0282swap=true := by decide +kernel
theorem certified0282swap : Certified (graph core0282) (root 6) 2 1 :=
  of_native_maps core0282 DegreeOneSmallSpectrum494.graph DegreeOneSmallSpectrum378.graph
    sourceMap0282swap fusedMap0282swap sourceMap0282swap_checked fusedMap0282swap_checked
    DegreeOneSmallComparisons.comparison0282
#print axioms sourceMap0282swap_checked
#print axioms fusedMap0282swap_checked
#print axioms certified0282swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
