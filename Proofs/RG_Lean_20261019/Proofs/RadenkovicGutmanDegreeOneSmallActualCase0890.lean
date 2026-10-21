/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0890 : Family 8 := level8.get ⟨49,by decide⟩
def sourceMap0890 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,11,12,7,8,9,10] (sourceLabel 8 1 1 v)
def fusedMap0890 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0890_checked : acceptsGraphIso
    (source (graph core0890) (root 8) 1 1) DegreeOneSmallSpectrum1255.graph sourceMap0890=true := by decide +kernel
theorem fusedMap0890_checked : acceptsGraphIso
    (fused (graph core0890) (root 8) 1 1) DegreeOneSmallSpectrum889.graph fusedMap0890=true := by decide +kernel
theorem certified0890 : Certified (graph core0890) (root 8) 1 1 :=
  of_native_maps core0890 DegreeOneSmallSpectrum1255.graph DegreeOneSmallSpectrum889.graph
    sourceMap0890 fusedMap0890 sourceMap0890_checked fusedMap0890_checked
    DegreeOneSmallComparisons.comparison0890
#print axioms sourceMap0890_checked
#print axioms fusedMap0890_checked
#print axioms certified0890
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
