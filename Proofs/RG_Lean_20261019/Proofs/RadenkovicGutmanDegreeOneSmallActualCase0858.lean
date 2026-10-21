/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0858 : Family 8 := level8.get ⟨39,by decide⟩
def sourceMap0858 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0858 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0858_checked : acceptsGraphIso
    (source (graph core0858) (root 8) 1 1) DegreeOneSmallSpectrum1105.graph sourceMap0858=true := by decide +kernel
theorem fusedMap0858_checked : acceptsGraphIso
    (fused (graph core0858) (root 8) 1 1) DegreeOneSmallSpectrum871.graph fusedMap0858=true := by decide +kernel
theorem certified0858 : Certified (graph core0858) (root 8) 1 1 :=
  of_native_maps core0858 DegreeOneSmallSpectrum1105.graph DegreeOneSmallSpectrum871.graph
    sourceMap0858 fusedMap0858 sourceMap0858_checked fusedMap0858_checked
    DegreeOneSmallComparisons.comparison0858
#print axioms sourceMap0858_checked
#print axioms fusedMap0858_checked
#print axioms certified0858
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
