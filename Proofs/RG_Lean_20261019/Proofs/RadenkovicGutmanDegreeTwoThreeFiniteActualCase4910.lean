/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4910 : Family 10 := level10.get ⟨1390,by decide⟩
def sourceMap4910 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4910 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4910_checked : acceptsGraphIso
    (source (graph core4910) (root 10) 2 2) DegreeTwoThreeSpectrum7148.graph sourceMap4910=true := by decide +kernel
theorem fusedMap4910_checked : acceptsGraphIso
    (fused (graph core4910) (root 10) 2 2) DegreeTwoThreeSpectrum6753.graph fusedMap4910=true := by decide +kernel
theorem certified4910 : Certified (graph core4910) (root 10) 2 2 :=
  of_native_maps core4910 DegreeTwoThreeSpectrum7148.graph DegreeTwoThreeSpectrum6753.graph
    sourceMap4910 fusedMap4910 sourceMap4910_checked fusedMap4910_checked
    DegreeTwoThreeFiniteComparisons.comparison4910
#print axioms sourceMap4910_checked
#print axioms fusedMap4910_checked
#print axioms certified4910
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
