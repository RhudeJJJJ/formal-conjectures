/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2127 : Family 10 := level10.get ⟨566,by decide⟩
def sourceMap2127 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2127 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2127_checked : acceptsGraphIso
    (source (graph core2127) (root 10) 0 0) DegreeOneSmallSpectrum1746.graph sourceMap2127=true := by decide +kernel
theorem fusedMap2127_checked : acceptsGraphIso
    (fused (graph core2127) (root 10) 0 0) DegreeOneSmallSpectrum1094.graph fusedMap2127=true := by decide +kernel
theorem certified2127 : Certified (graph core2127) (root 10) 0 0 :=
  of_native_maps core2127 DegreeOneSmallSpectrum1746.graph DegreeOneSmallSpectrum1094.graph
    sourceMap2127 fusedMap2127 sourceMap2127_checked fusedMap2127_checked
    DegreeOneSmallComparisons.comparison2127
#print axioms sourceMap2127_checked
#print axioms fusedMap2127_checked
#print axioms certified2127
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
