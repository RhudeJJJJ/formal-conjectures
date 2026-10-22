/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4786 : Family 10 := level10.get ⟨1097,by decide⟩
def sourceMap4786 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4786 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4786_checked : acceptsGraphIso
    (source (graph core4786) (root 10) 2 2) DegreeTwoThreeSpectrum7177.graph sourceMap4786=true := by decide +kernel
theorem fusedMap4786_checked : acceptsGraphIso
    (fused (graph core4786) (root 10) 2 2) DegreeTwoThreeSpectrum6178.graph fusedMap4786=true := by decide +kernel
theorem certified4786 : Certified (graph core4786) (root 10) 2 2 :=
  of_native_maps core4786 DegreeTwoThreeSpectrum7177.graph DegreeTwoThreeSpectrum6178.graph
    sourceMap4786 fusedMap4786 sourceMap4786_checked fusedMap4786_checked
    DegreeTwoThreeFiniteComparisons.comparison4786
#print axioms sourceMap4786_checked
#print axioms fusedMap4786_checked
#print axioms certified4786
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
