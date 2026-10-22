/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4454 : Family 10 := level10.get ⟨117,by decide⟩
def sourceMap4454 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4454 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4454_checked : acceptsGraphIso
    (source (graph core4454) (root 10) 2 2) DegreeTwoThreeSpectrum6784.graph sourceMap4454=true := by decide +kernel
theorem fusedMap4454_checked : acceptsGraphIso
    (fused (graph core4454) (root 10) 2 2) DegreeTwoThreeSpectrum5044.graph fusedMap4454=true := by decide +kernel
theorem certified4454 : Certified (graph core4454) (root 10) 2 2 :=
  of_native_maps core4454 DegreeTwoThreeSpectrum6784.graph DegreeTwoThreeSpectrum5044.graph
    sourceMap4454 fusedMap4454 sourceMap4454_checked fusedMap4454_checked
    DegreeTwoThreeFiniteComparisons.comparison4454
#print axioms sourceMap4454_checked
#print axioms fusedMap4454_checked
#print axioms certified4454
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
