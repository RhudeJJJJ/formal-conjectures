/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0951 : Family 8 := level8.get ⟨75,by decide⟩
def sourceMap0951 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0951 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0951_checked : acceptsGraphIso
    (source (graph core0951) (root 8) 0 0) SmallGeFourSpectrum054.graph sourceMap0951=true := by decide +kernel
theorem fusedMap0951_checked : acceptsGraphIso
    (fused (graph core0951) (root 8) 0 0) SmallGeFourSpectrum039.graph fusedMap0951=true := by decide +kernel
theorem certified0951 : Certified (graph core0951) (root 8) 0 0 :=
  of_native_maps core0951 SmallGeFourSpectrum054.graph SmallGeFourSpectrum039.graph
    sourceMap0951 fusedMap0951 sourceMap0951_checked fusedMap0951_checked
    DegreeOneSmallComparisons.comparison0951
#print axioms sourceMap0951_checked
#print axioms fusedMap0951_checked
#print axioms certified0951
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
