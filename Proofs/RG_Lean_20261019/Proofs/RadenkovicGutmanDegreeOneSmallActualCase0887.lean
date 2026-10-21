/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0887 : Family 8 := level8.get ⟨49,by decide⟩
def sourceMap0887 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (sourceLabel 8 0 0 v)
def fusedMap0887 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap0887_checked : acceptsGraphIso
    (source (graph core0887) (root 8) 0 0) DegreeOneSmallSpectrum287.graph sourceMap0887=true := by decide +kernel
theorem fusedMap0887_checked : acceptsGraphIso
    (fused (graph core0887) (root 8) 0 0) DegreeOneSmallSpectrum195.graph fusedMap0887=true := by decide +kernel
theorem certified0887 : Certified (graph core0887) (root 8) 0 0 :=
  of_native_maps core0887 DegreeOneSmallSpectrum287.graph DegreeOneSmallSpectrum195.graph
    sourceMap0887 fusedMap0887 sourceMap0887_checked fusedMap0887_checked
    DegreeOneSmallComparisons.comparison0887
#print axioms sourceMap0887_checked
#print axioms fusedMap0887_checked
#print axioms certified0887
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
