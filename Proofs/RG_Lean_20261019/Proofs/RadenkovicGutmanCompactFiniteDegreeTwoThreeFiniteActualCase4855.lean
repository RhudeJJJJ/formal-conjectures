/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4855 : Family 10 := level10.get ⟨1265,by decide⟩
def sourceMap4855 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4855 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4855_checked : acceptsGraphIso
    (source (graph core4855) (root 10) 2 2) DegreeTwoThreeSpectrum7347.graph sourceMap4855=true := by decide +kernel
theorem fusedMap4855_checked : acceptsGraphIso
    (fused (graph core4855) (root 10) 2 2) DegreeTwoThreeSpectrum6519.graph fusedMap4855=true := by decide +kernel
theorem certified4855 : Certified (graph core4855) (root 10) 2 2 :=
  of_native_maps core4855 DegreeTwoThreeSpectrum7347.graph DegreeTwoThreeSpectrum6519.graph
    sourceMap4855 fusedMap4855 sourceMap4855_checked fusedMap4855_checked
    DegreeTwoThreeFiniteComparisons.comparison4855
#print axioms sourceMap4855_checked
#print axioms fusedMap4855_checked
#print axioms certified4855
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
