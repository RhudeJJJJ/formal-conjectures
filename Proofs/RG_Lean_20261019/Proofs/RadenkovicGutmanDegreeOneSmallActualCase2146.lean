/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2146 : Family 10 := level10.get ⟨596,by decide⟩
def sourceMap2146 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2146 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2146_checked : acceptsGraphIso
    (source (graph core2146) (root 10) 0 0) DegreeOneSmallSpectrum1812.graph sourceMap2146=true := by decide +kernel
theorem fusedMap2146_checked : acceptsGraphIso
    (fused (graph core2146) (root 10) 0 0) DegreeOneSmallSpectrum1146.graph fusedMap2146=true := by decide +kernel
theorem certified2146 : Certified (graph core2146) (root 10) 0 0 :=
  of_native_maps core2146 DegreeOneSmallSpectrum1812.graph DegreeOneSmallSpectrum1146.graph
    sourceMap2146 fusedMap2146 sourceMap2146_checked fusedMap2146_checked
    DegreeOneSmallComparisons.comparison2146
#print axioms sourceMap2146_checked
#print axioms fusedMap2146_checked
#print axioms certified2146
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
