/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0621 : Family 7 := level7.get ⟨42,by decide⟩
def sourceMap0621 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (sourceLabel 7 0 0 v)
def fusedMap0621 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0621_checked : acceptsGraphIso
    (source (graph core0621) (root 7) 0 0) SmallGeFourSpectrum018.graph sourceMap0621=true := by decide +kernel
theorem fusedMap0621_checked : acceptsGraphIso
    (fused (graph core0621) (root 7) 0 0) SmallGeFourSpectrum022.graph fusedMap0621=true := by decide +kernel
theorem certified0621 : Certified (graph core0621) (root 7) 0 0 :=
  of_native_maps core0621 SmallGeFourSpectrum018.graph SmallGeFourSpectrum022.graph
    sourceMap0621 fusedMap0621 sourceMap0621_checked fusedMap0621_checked
    DegreeOneSmallComparisons.comparison0621
#print axioms sourceMap0621_checked
#print axioms fusedMap0621_checked
#print axioms certified0621
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
